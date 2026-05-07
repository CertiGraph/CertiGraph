#!/usr/bin/env python3
"""
Compute project-scoped statistics from Codex rollout JSONL transcripts.

This parser is intentionally conservative:
- it only counts rollout items whose session cwd/workspace is the requested repo;
- it counts response_item tool calls once, not streamed token deltas;
- it excludes automatic <environment_context> user messages from human prompts;
- it does not print prompt or assistant-message bodies.

Example:
  python3 tools/rollout_jsonl_stats.py rollout-*.jsonl \
    --cwd /Users/shengyiwang/Library/CloudStorage/Dropbox/Program/Coq/CertiGraph \
    --timezone Asia/Shanghai --out codex-rollout-stats.md
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

try:
    from zoneinfo import ZoneInfo
except ImportError:  # pragma: no cover
    ZoneInfo = None


BUILD_RE = re.compile(
    r"(^|[;&|]\s*)(?:(?:env\s+\S+\s+)*|(?:opam\s+exec(?:\s+\S+)*\s+--\s+))?"
    r"(?:make|gmake|rocqc|coqc|rocq|dune|latexmk|pdflatex|bibtex)\b"
)
SEARCH_RE = re.compile(r"(^|[;&|]\s*)(?:rg|grep|git\s+grep|ag|ack|find)\b")
READ_RE = re.compile(
    r"(^|[;&|]\s*)(?:sed|cat|nl|head|tail|ls|find|wc|pwd|"
    r"git\s+(?:status|show|log|diff|branch|rev-parse|rev-list|shortlog))\b"
)
COMMIT_RE = re.compile(r"\bgit\s+commit\b")

KEY_FILES = [
    "CertiGC/GCGraph.v",
    "CertiGC/gc_correct.v",
    "CertiGC/gc_spec.v",
    "CertiGC/spatial_gcgraph.v",
    "CertiGC/verif_do_generation.v",
    "CertiGC/verif_garbage_collect.v",
    "CertiGC/verif_forward_remset.v",
    "CertiGC/forward_lemmas.v",
    "CertiGC/gc_correct_refactor_notes.md",
]


def parse_timestamp(raw: str, tz: dt.tzinfo) -> dt.datetime:
    value = raw.replace("Z", "+00:00")
    parsed = dt.datetime.fromisoformat(value)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=dt.timezone.utc)
    return parsed.astimezone(tz)


def text_of_content(content: Any) -> str:
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts = []
        for item in content:
            if isinstance(item, dict):
                parts.append(str(item.get("text") or ""))
        return "\n".join(parts)
    return ""


def json_args(payload: dict[str, Any]) -> dict[str, Any]:
    args = payload.get("arguments")
    if not isinstance(args, str) or not args.strip():
        return {}
    try:
        value = json.loads(args)
    except json.JSONDecodeError:
        return {}
    return value if isinstance(value, dict) else {}


def normalize_path(path: str, cwd: str) -> str:
    if path.startswith(cwd + "/"):
        return path[len(cwd) + 1 :]
    return path


def patch_files(patch: str, cwd: str) -> list[str]:
    files = []
    for line in patch.splitlines():
        m = re.match(r"\*\*\* (?:Add|Update|Delete) File: (.+)$", line)
        if m:
            files.append(normalize_path(m.group(1).strip(), cwd))
    return files


def command_files(command: str) -> set[str]:
    files = set()
    for key in KEY_FILES:
        if key in command:
            files.add(key)
    for m in re.finditer(r"\bCertiGC/[A-Za-z0-9_./-]+\.(?:v|vo|md|c|h)\b", command):
        value = m.group(0)
        if value.endswith(".vo"):
            value = value[:-3] + ".v"
        files.add(value)
    return files


def active_hours(timestamps: list[dt.datetime], gap_minutes: int) -> float:
    if len(timestamps) < 2:
        return 0.0
    ordered = sorted(set(timestamps))
    total = dt.timedelta()
    gap = dt.timedelta(minutes=gap_minutes)
    for prev, cur in zip(ordered, ordered[1:]):
        delta = cur - prev
        if dt.timedelta(0) <= delta <= gap:
            total += delta
    return total.total_seconds() / 3600.0


def wall_hours(timestamps: list[dt.datetime]) -> float:
    if len(timestamps) < 2:
        return 0.0
    ordered = sorted(timestamps)
    return (ordered[-1] - ordered[0]).total_seconds() / 3600.0


def summed_day_wall_hours(stats: "RolloutStats") -> float:
    return sum(wall_hours(times) for times in stats.per_day_timestamps.values())


def summed_day_active_hours(stats: "RolloutStats") -> float:
    return sum(active_hours(times, stats.gap_minutes) for times in stats.per_day_timestamps.values())


def total_tool_calls(counts: Counter[str]) -> int:
    return counts["function_tool_calls"] + counts["custom_tool_calls"] + counts["web_search_calls"]


def hours(value: float) -> str:
    return f"{value:.1f}"


@dataclass
class FileStats:
    patch_calls: int = 0
    compile_calls: int = 0
    shell_refs: int = 0
    rocq_refs: int = 0


@dataclass
class RolloutStats:
    cwd: str
    gap_minutes: int
    date_from: dt.date | None = None
    date_to: dt.date | None = None
    counts: Counter[str] = field(default_factory=Counter)
    response_item_types: Counter[str] = field(default_factory=Counter)
    event_types: Counter[str] = field(default_factory=Counter)
    function_names: Counter[str] = field(default_factory=Counter)
    custom_tool_names: Counter[str] = field(default_factory=Counter)
    commands: Counter[str] = field(default_factory=Counter)
    shell_build_commands: Counter[str] = field(default_factory=Counter)
    shell_search_commands: Counter[str] = field(default_factory=Counter)
    shell_read_commands: Counter[str] = field(default_factory=Counter)
    files: dict[str, FileStats] = field(default_factory=lambda: defaultdict(FileStats))
    all_timestamps: list[dt.datetime] = field(default_factory=list)
    metric_timestamps: dict[str, list[dt.datetime]] = field(default_factory=lambda: defaultdict(list))
    per_day: dict[str, Counter[str]] = field(default_factory=lambda: defaultdict(Counter))
    per_day_timestamps: dict[str, list[dt.datetime]] = field(default_factory=lambda: defaultdict(list))
    session_ids: set[str] = field(default_factory=set)
    models: Counter[str] = field(default_factory=Counter)
    input_files: dict[str, int] = field(default_factory=dict)
    first_timestamp: dt.datetime | None = None
    last_timestamp: dt.datetime | None = None

    def bump(self, key: str, ts: dt.datetime | None = None) -> None:
        self.counts[key] += 1
        if ts is not None:
            self.metric_timestamps[key].append(ts)
            self.per_day[ts.date().isoformat()][key] += 1

    def add_activity(self, ts: dt.datetime) -> None:
        self.all_timestamps.append(ts)
        day = ts.date().isoformat()
        self.per_day_timestamps[day].append(ts)
        self.first_timestamp = ts if self.first_timestamp is None else min(self.first_timestamp, ts)
        self.last_timestamp = ts if self.last_timestamp is None else max(self.last_timestamp, ts)

    def add_file(self, path: str, kind: str) -> None:
        fs = self.files[path]
        if kind == "patch":
            fs.patch_calls += 1
        elif kind == "compile":
            fs.compile_calls += 1
        elif kind == "rocq":
            fs.rocq_refs += 1
        elif kind == "shell":
            fs.shell_refs += 1


def analyze_file(path: Path, stats: RolloutStats, tz: dt.tzinfo) -> None:
    stats.input_files[path.name] = 0
    session_cwd = None
    session_relevant = False

    with path.open(encoding="utf-8", errors="replace") as fh:
        for line in fh:
            stats.input_files[path.name] += 1
            obj = json.loads(line)
            raw_ts = obj.get("timestamp")
            ts = parse_timestamp(raw_ts, tz) if isinstance(raw_ts, str) else None
            if ts is not None:
                event_day = ts.date()
                if stats.date_from is not None and event_day < stats.date_from:
                    continue
                if stats.date_to is not None and event_day > stats.date_to:
                    continue
            if ts is not None:
                stats.add_activity(ts)

            top_type = obj.get("type")
            payload = obj.get("payload") if isinstance(obj.get("payload"), dict) else {}

            if top_type == "session_meta":
                session_cwd = payload.get("cwd")
                session_relevant = session_cwd == stats.cwd
                sid = payload.get("id")
                if sid:
                    stats.session_ids.add(str(sid))
                if payload.get("model_provider"):
                    stats.counts[f"provider:{payload['model_provider']}"] += 1
                continue

            if not session_relevant:
                continue

            if top_type == "compacted":
                stats.bump("context_compactions", ts)
                continue

            if top_type == "event_msg":
                ev = payload.get("type")
                if ev:
                    stats.event_types[str(ev)] += 1
                if ev == "task_started":
                    stats.bump("turns_started", ts)
                elif ev == "task_complete":
                    stats.bump("turns_completed", ts)
                elif ev == "turn_aborted":
                    stats.bump("turns_aborted", ts)
                elif ev == "context_compacted":
                    # Count top-level compacted records as the authoritative value.
                    pass
                return_code = payload.get("exit_code")
                if return_code not in (None, 0, "0"):
                    stats.bump("nonzero_tool_results", ts)
                continue

            if top_type != "response_item":
                continue

            item_type = payload.get("type")
            if item_type:
                stats.response_item_types[str(item_type)] += 1

            if item_type == "message":
                role = payload.get("role")
                text = text_of_content(payload.get("content"))
                if role == "user":
                    if text.strip().startswith("<environment_context>"):
                        stats.bump("environment_context_messages", ts)
                    else:
                        stats.bump("human_prompts", ts)
                elif role == "assistant":
                    stats.bump("assistant_messages", ts)
                continue

            if item_type == "function_call":
                name = str(payload.get("name") or "")
                stats.function_names[name] += 1
                stats.bump("function_tool_calls", ts)
                if name.startswith("rocq_"):
                    stats.bump("rocq_mcp_calls", ts)
                if name in {"rocq_check", "rocq_compile_file", "rocq_compile"}:
                    stats.bump("proof_checking_invocations", ts)

                args = json_args(payload)
                file_arg = args.get("file")
                if isinstance(file_arg, str):
                    norm = normalize_path(file_arg, stats.cwd)
                    stats.add_file(norm, "rocq")
                    if name == "rocq_compile_file":
                        stats.add_file(norm, "compile")

                if name == "exec_command":
                    stats.bump("shell_exec_calls", ts)
                    cmd = str(args.get("cmd") or "")
                    compact = " ".join(cmd.split())
                    if compact:
                        stats.commands[compact] += 1
                    for f in command_files(compact):
                        stats.add_file(f, "shell")
                    if BUILD_RE.search(compact):
                        stats.bump("shell_build_commands", ts)
                        stats.bump("proof_checking_invocations", ts)
                        stats.shell_build_commands[compact] += 1
                        for f in command_files(compact):
                            stats.add_file(f, "compile")
                    if SEARCH_RE.search(compact):
                        stats.bump("shell_search_commands", ts)
                        stats.shell_search_commands[compact] += 1
                    if READ_RE.search(compact):
                        stats.bump("shell_read_commands", ts)
                        stats.shell_read_commands[compact] += 1
                    if COMMIT_RE.search(compact):
                        stats.bump("git_commit_commands", ts)
                elif name == "write_stdin":
                    stats.bump("shell_session_inputs", ts)
                continue

            if item_type == "custom_tool_call":
                name = str(payload.get("name") or "")
                stats.custom_tool_names[name] += 1
                stats.bump("custom_tool_calls", ts)
                if name == "apply_patch":
                    stats.bump("apply_patch_calls", ts)
                    patch = str(payload.get("input") or "")
                    for f in patch_files(patch, stats.cwd):
                        stats.add_file(f, "patch")
                continue

            if item_type == "web_search_call":
                stats.bump("web_search_calls", ts)


def emit_markdown(stats: RolloutStats) -> str:
    lines = []
    lines.append("# Codex Rollout Statistics")
    lines.append("")
    lines.append("Scope:")
    lines.append(f"- CWD filter: `{stats.cwd}`")
    lines.append("- Sources: " + ", ".join(f"`{name}` ({count} lines)" for name, count in stats.input_files.items()))
    lines.append("- Human prompts exclude automatic `<environment_context>` messages.")
    lines.append("- Tool calls count rollout `response_item` call records once; streamed deltas and outputs are not counted as calls.")
    lines.append(f"- Active hours exclude gaps longer than {stats.gap_minutes} minutes.")
    if stats.date_from is not None or stats.date_to is not None:
        start = stats.date_from.isoformat() if stats.date_from else "beginning"
        end = stats.date_to.isoformat() if stats.date_to else "end"
        lines.append(f"- Date filter: `{start}` to `{end}` in the selected timezone.")
    lines.append("")
    if stats.first_timestamp and stats.last_timestamp:
        lines.append("Overall time:")
        lines.append(f"- First event: {stats.first_timestamp.isoformat()}")
        lines.append(f"- Last event: {stats.last_timestamp.isoformat()}")
        lines.append(f"- Calendar-span hours: {hours(wall_hours(stats.all_timestamps))}")
        lines.append(f"- Wall-clock hours (sum of per-day spans): {hours(summed_day_wall_hours(stats))}")
        lines.append(f"- Active hours: {hours(summed_day_active_hours(stats))}")
        lines.append("")

    lines.append("## Aggregate Counts")
    rows = [
        ("Human prompts", stats.counts["human_prompts"]),
        ("Assistant messages", stats.counts["assistant_messages"]),
        ("Context compactions", stats.counts["context_compactions"]),
        ("Function tool calls", stats.counts["function_tool_calls"]),
        ("Custom tool calls", stats.counts["custom_tool_calls"]),
        ("Web search calls", stats.counts["web_search_calls"]),
        ("Total tool calls", total_tool_calls(stats.counts)),
        ("Shell exec calls", stats.counts["shell_exec_calls"]),
        ("Shell session inputs", stats.counts["shell_session_inputs"]),
        ("Rocq MCP calls", stats.counts["rocq_mcp_calls"]),
        ("Proof-checking invocations", stats.counts["proof_checking_invocations"]),
        ("Shell build commands", stats.counts["shell_build_commands"]),
        ("Shell search commands", stats.counts["shell_search_commands"]),
        ("Shell read/inspection commands", stats.counts["shell_read_commands"]),
        ("Apply-patch edit calls", stats.counts["apply_patch_calls"]),
        ("Git commit commands", stats.counts["git_commit_commands"]),
        ("Calendar-span hours", hours(wall_hours(stats.all_timestamps))),
        ("Wall-clock hours (per-day sum)", hours(summed_day_wall_hours(stats))),
        ("Active hours", hours(summed_day_active_hours(stats))),
        ("Turns started", stats.counts["turns_started"]),
        ("Turns completed", stats.counts["turns_completed"]),
        ("Turns aborted", stats.counts["turns_aborted"]),
    ]
    lines.append("| Metric | Count |")
    lines.append("|---|---:|")
    for label, value in rows:
        lines.append(f"| {label} | {value} |")
    lines.append("")

    lines.append("## Zoe-Style Per-Day Development Activity")
    headers = [
        "Date",
        "Prompts",
        "Compactions",
        "Total tools",
        "Shell",
        "Shell inputs",
        "Rocq MCP",
        "Proof checks",
        "Build",
        "Search",
        "Read",
        "Patch",
        "Git commits",
        "Wall h",
        "Active h",
    ]
    lines.append("| " + " | ".join(headers) + " |")
    lines.append("|" + "|".join("---" if i == 0 else "---:" for i in range(len(headers))) + "|")
    for day in sorted(stats.per_day_timestamps):
        c = stats.per_day[day]
        row = [
            day,
            str(c["human_prompts"]),
            str(c["context_compactions"]),
            str(total_tool_calls(c)),
            str(c["shell_exec_calls"]),
            str(c["shell_session_inputs"]),
            str(c["rocq_mcp_calls"]),
            str(c["proof_checking_invocations"]),
            str(c["shell_build_commands"]),
            str(c["shell_search_commands"]),
            str(c["shell_read_commands"]),
            str(c["apply_patch_calls"]),
            str(c["git_commit_commands"]),
            hours(wall_hours(stats.per_day_timestamps[day])),
            hours(active_hours(stats.per_day_timestamps[day], stats.gap_minutes)),
        ]
        lines.append("| " + " | ".join(row) + " |")
    total_row = [
        "Total",
        str(stats.counts["human_prompts"]),
        str(stats.counts["context_compactions"]),
        str(total_tool_calls(stats.counts)),
        str(stats.counts["shell_exec_calls"]),
        str(stats.counts["shell_session_inputs"]),
        str(stats.counts["rocq_mcp_calls"]),
        str(stats.counts["proof_checking_invocations"]),
        str(stats.counts["shell_build_commands"]),
        str(stats.counts["shell_search_commands"]),
        str(stats.counts["shell_read_commands"]),
        str(stats.counts["apply_patch_calls"]),
        str(stats.counts["git_commit_commands"]),
        hours(summed_day_wall_hours(stats)),
        hours(summed_day_active_hours(stats)),
    ]
    lines.append("| " + " | ".join(total_row) + " |")
    lines.append("")

    lines.append("## Tool Breakdown")
    lines.append("| Function tool | Count |")
    lines.append("|---|---:|")
    for name, count in stats.function_names.most_common():
        lines.append(f"| `{name}` | {count} |")
    lines.append("")
    if stats.custom_tool_names:
        lines.append("| Custom tool | Count |")
        lines.append("|---|---:|")
        for name, count in stats.custom_tool_names.most_common():
            lines.append(f"| `{name}` | {count} |")
        lines.append("")

    lines.append("## File Activity")
    lines.append("| File | Patch calls | Compile calls | Rocq refs | Shell refs |")
    lines.append("|---|---:|---:|---:|---:|")
    file_rows = sorted(
        stats.files.items(),
        key=lambda kv: (kv[1].patch_calls + kv[1].compile_calls + kv[1].rocq_refs + kv[1].shell_refs, kv[0]),
        reverse=True,
    )
    for path, fs in file_rows[:30]:
        lines.append(f"| `{path}` | {fs.patch_calls} | {fs.compile_calls} | {fs.rocq_refs} | {fs.shell_refs} |")
    lines.append("")

    lines.append("## Top Shell Build Commands")
    lines.append("| Count | Command |")
    lines.append("|---:|---|")
    for cmd, count in stats.shell_build_commands.most_common(25):
        lines.append(f"| {count} | `{cmd}` |")
    lines.append("")

    lines.append("## Top Shell Commands")
    lines.append("| Count | Command |")
    lines.append("|---:|---|")
    for cmd, count in stats.commands.most_common(25):
        lines.append(f"| {count} | `{cmd}` |")
    lines.append("")

    lines.append("## Notes")
    lines.append("- `Rocq MCP calls` are a subset of `Function tool calls`; they are not added again when computing `Total tool calls`.")
    lines.append("- `Proof-checking invocations` counts `rocq_check`, `rocq_compile_file`, `rocq_compile`, and shell build/proof commands.")
    lines.append("- `Shell read/inspection commands` is a heuristic category for commands such as `sed`, `cat`, `ls`, `git diff`, and `git log`; it is not directly comparable to Claude Code's dedicated Read tool.")
    lines.append("- `File Activity` counts patch calls and references, not lines changed.")
    return "\n".join(lines) + "\n"


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("jsonl", nargs="+", type=Path)
    parser.add_argument("--cwd", required=True)
    parser.add_argument("--timezone", default="Asia/Shanghai")
    parser.add_argument("--gap-minutes", type=int, default=30)
    parser.add_argument("--date-from", type=dt.date.fromisoformat)
    parser.add_argument("--date-to", type=dt.date.fromisoformat)
    parser.add_argument("--out", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if ZoneInfo is None:
        tz = dt.timezone.utc
    else:
        tz = ZoneInfo(args.timezone)
    stats = RolloutStats(
        cwd=args.cwd,
        gap_minutes=args.gap_minutes,
        date_from=args.date_from,
        date_to=args.date_to,
    )
    for path in args.jsonl:
        if not path.exists():
            print(f"missing input: {path}", file=sys.stderr)
            return 2
        analyze_file(path, stats, tz)
    output = emit_markdown(stats)
    if args.out:
        args.out.write_text(output, encoding="utf-8")
    else:
        print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

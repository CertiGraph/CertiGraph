# Codex Rollout Statistics

Scope:
- CWD filter: `/Users/shengyiwang/Library/CloudStorage/Dropbox/Program/Coq/CertiGraph`
- Sources: `rollout-2026-04-22T15-16-15-019db40b-f475-72c3-9aba-52c2ea0545a7.jsonl` (58516 lines), `rollout-2026-05-01T12-44-05-019de1d9-df45-71e2-a387-e830b2957cae.jsonl` (5483 lines)
- Human prompts exclude automatic `<environment_context>` messages.
- Tool calls count rollout `response_item` call records once; streamed deltas and outputs are not counted as calls.
- Active hours exclude gaps longer than 30 minutes.
- Date filter: `beginning` to `2026-05-03` in the selected timezone.

Overall time:
- First event: 2026-04-22T15:19:37.712000+08:00
- Last event: 2026-05-03T17:10:53.760000+08:00
- Calendar-span hours: 265.9
- Wall-clock hours (sum of per-day spans): 106.5
- Active hours: 59.3

## Aggregate Counts
| Metric | Count |
|---|---:|
| Human prompts | 415 |
| Assistant messages | 2237 |
| Context compactions | 88 |
| Function tool calls | 11566 |
| Custom tool calls | 1731 |
| Web search calls | 8 |
| Total tool calls | 13305 |
| Shell exec calls | 8077 |
| Shell session inputs | 1368 |
| Rocq MCP calls | 2096 |
| Proof-checking invocations | 2131 |
| Shell build commands | 795 |
| Shell search commands | 2018 |
| Shell read/inspection commands | 5337 |
| Apply-patch edit calls | 1731 |
| Git commit commands | 80 |
| Calendar-span hours | 265.9 |
| Wall-clock hours (per-day sum) | 106.5 |
| Active hours | 59.3 |
| Turns started | 349 |
| Turns completed | 347 |
| Turns aborted | 2 |

## Zoe-Style Per-Day Development Activity
| Date | Prompts | Compactions | Total tools | Shell | Shell inputs | Rocq MCP | Proof checks | Build | Search | Read | Patch | Git commits | Wall h | Active h |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2026-04-22 | 24 | 2 | 539 | 384 | 74 | 20 | 67 | 60 | 111 | 210 | 54 | 4 | 5.7 | 2.9 |
| 2026-04-23 | 2 | 0 | 52 | 32 | 1 | 18 | 17 | 1 | 11 | 20 | 1 | 0 | 0.8 | 0.8 |
| 2026-04-26 | 42 | 8 | 1750 | 912 | 346 | 255 | 303 | 212 | 195 | 482 | 234 | 10 | 9.0 | 7.6 |
| 2026-04-27 | 58 | 15 | 2499 | 1326 | 417 | 503 | 474 | 168 | 342 | 878 | 250 | 20 | 14.1 | 10.1 |
| 2026-04-28 | 93 | 26 | 3070 | 1837 | 32 | 727 | 602 | 82 | 516 | 1296 | 465 | 7 | 23.0 | 12.8 |
| 2026-04-29 | 62 | 23 | 2705 | 1657 | 118 | 546 | 402 | 29 | 440 | 1215 | 381 | 11 | 21.4 | 10.8 |
| 2026-04-30 | 53 | 4 | 759 | 536 | 129 | 4 | 61 | 57 | 102 | 311 | 82 | 9 | 11.6 | 4.9 |
| 2026-05-01 | 43 | 6 | 1031 | 686 | 211 | 0 | 110 | 110 | 153 | 447 | 134 | 5 | 10.8 | 4.9 |
| 2026-05-02 | 20 | 2 | 487 | 401 | 2 | 12 | 60 | 52 | 79 | 262 | 72 | 6 | 5.3 | 2.1 |
| 2026-05-03 | 18 | 2 | 413 | 306 | 38 | 11 | 35 | 24 | 69 | 216 | 58 | 8 | 4.8 | 2.3 |
| Total | 415 | 88 | 13305 | 8077 | 1368 | 2096 | 2131 | 795 | 2018 | 5337 | 1731 | 80 | 106.5 | 59.3 |

## Tool Breakdown
| Function tool | Count |
|---|---:|
| `exec_command` | 8077 |
| `write_stdin` | 1368 |
| `rocq_check` | 712 |
| `rocq_compile_file` | 595 |
| `rocq_start` | 405 |
| `rocq_query` | 321 |
| `rocq_compile` | 29 |
| `rocq_step_multi` | 27 |
| `update_plan` | 18 |
| `rocq_toc` | 6 |
| `list_mcp_resources` | 3 |
| `list_mcp_resource_templates` | 3 |
| `wait_agent` | 1 |
| `rocq_assumptions` | 1 |

| Custom tool | Count |
|---|---:|
| `apply_patch` | 1731 |

## File Activity
| File | Patch calls | Compile calls | Rocq refs | Shell refs |
|---|---:|---:|---:|---:|
| `CertiGC/gc_correct.v` | 836 | 672 | 907 | 2677 |
| `CertiGC/GCGraph.v` | 384 | 225 | 115 | 3003 |
| `CertiGC/verif_garbage_collect.v` | 226 | 224 | 120 | 747 |
| `CertiGC/verif_do_generation.v` | 131 | 134 | 72 | 437 |
| `CertiGC/gc_spec.v` | 34 | 21 | 9 | 350 |
| `CertiGC/spatial_gcgraph.v` | 19 | 3 | 8 | 211 |
| `CertiGC/verif_do_scan.v` | 28 | 31 | 34 | 86 |
| `CertiGC/gc_correct_refactor_notes.md` | 34 | 0 | 0 | 114 |
| `CertiGC/verif_create_heap.v` | 7 | 10 | 12 | 25 |
| `CertiGC/verif_forward_remset.v` | 1 | 3 | 0 | 27 |
| `CertiGC/verif_forward2.v` | 4 | 6 | 0 | 18 |
| `CertiGC/verif_forward1.v` | 5 | 6 | 0 | 17 |
| `CertiGC/GC_Source/gc_stack.c` | 0 | 0 | 0 | 28 |
| `CertiGC/verif_forward_roots.v` | 1 | 3 | 0 | 20 |
| `CertiGC/forward_lemmas.v` | 1 | 0 | 0 | 19 |
| `CertiGC/verif_Is_from.v` | 1 | 3 | 0 | 14 |
| `CertiGC/gc_stack.v` | 0 | 0 | 0 | 13 |
| `CertiGC/verif_resume.v` | 0 | 2 | 0 | 5 |
| `CertiGC/data_at_test.v` | 0 | 1 | 0 | 6 |
| `CertiGC/verif_forward.v` | 0 | 2 | 0 | 4 |
| `CertiGC/env_graph_gc.v` | 0 | 0 | 0 | 6 |
| `CertiGC/verif_make_tinfo.v` | 0 | 2 | 0 | 3 |
| `CertiGC/verif_is_ptr.v` | 0 | 2 | 0 | 3 |
| `CertiGC/verif_create_space.v` | 0 | 2 | 0 | 3 |
| `CertiGC/verif_conversion.v` | 0 | 2 | 0 | 3 |
| `Makefile` | 4 | 0 | 0 | 0 |
| `lib/List_ext.v` | 3 | 0 | 0 | 0 |
| `coq-certigraph.opam` | 3 | 0 | 0 | 0 |
| `README.md` | 3 | 0 | 0 | 0 |
| `append/verif_append.v` | 2 | 0 | 0 | 0 |

## Top Shell Build Commands
| Count | Command |
|---:|---|
| 208 | `make CertiGC/verif_garbage_collect.vo` |
| 163 | `make CertiGC/GCGraph.vo` |
| 122 | `make CertiGC/verif_do_generation.vo` |
| 119 | `make CertiGC/gc_correct.vo` |
| 27 | `make CertiGC/verif_do_scan.vo` |
| 25 | `make -j8` |
| 24 | `make -kj8` |
| 13 | `make CertiGC/gc_spec.vo` |
| 11 | `make -f CoqMakefile CertiGC/GCGraph.vo` |
| 8 | `make CertiGC/verif_create_heap.vo` |
| 5 | `opam exec --switch=certigraph -- make clean` |
| 5 | `opam exec --switch=certigraph -- make -j8` |
| 5 | `make -f CoqMakefile CertiGC/GCGraph.vo CertiGC/gc_correct.vo` |
| 4 | `make CertiGC/verif_forward1.vo` |
| 4 | `make CertiGC/verif_forward2.vo` |
| 3 | `make clean` |
| 3 | `make -j8 CertiGC/verif_garbage_collect.vo` |
| 3 | `make -n CertiGC/gc_correct.vo` |
| 2 | `make CertiGC/gc_spec.vo CertiGC/verif_do_scan.vo` |
| 2 | `make CertiGC/gc_spec.vo CertiGC/verif_do_generation.vo` |
| 2 | `make CertiGC/GCGraph.vo CertiGC/verif_garbage_collect.vo` |
| 2 | `make -f CoqMakefile CertiGC/gc_correct.vo` |
| 2 | `make -j8 > /private/tmp/certig_make_after_warnings.log 2>&1` |
| 2 | `make -j8 CertiGC/GCGraph.vo` |
| 1 | `coqc -v` |

## Top Shell Commands
| Count | Command |
|---:|---|
| 406 | `git status --short` |
| 208 | `make CertiGC/verif_garbage_collect.vo` |
| 193 | `git diff --stat` |
| 163 | `make CertiGC/GCGraph.vo` |
| 122 | `make CertiGC/verif_do_generation.vo` |
| 119 | `make CertiGC/gc_correct.vo` |
| 86 | `git diff --check` |
| 35 | `git status --short --branch` |
| 28 | `git diff -- CertiGC/gc_correct.v` |
| 27 | `make CertiGC/verif_do_scan.vo` |
| 25 | `make -j8` |
| 24 | `make -kj8` |
| 21 | `rg -n "\t" CertiGC/gc_correct.v` |
| 20 | `git diff --cached --stat` |
| 19 | `git diff --numstat` |
| 19 | `git diff --shortstat` |
| 17 | `git diff -- CertiGC/GCGraph.v` |
| 17 | `sed -n '1,220p' CertiGC/gc_correct_refactor_notes.md` |
| 17 | `git diff --stat -- CertiGC/gc_correct.v` |
| 15 | `git add CertiGC/gc_correct.v` |
| 13 | `make CertiGC/gc_spec.vo` |
| 13 | `wc -l CertiGC/gc_correct.v` |
| 12 | `git diff --check -- CertiGC/gc_correct.v` |
| 11 | `make -f CoqMakefile CertiGC/GCGraph.vo` |
| 10 | `git diff -- CertiGC/verif_do_generation.v` |

## Notes
- `Rocq MCP calls` are a subset of `Function tool calls`; they are not added again when computing `Total tool calls`.
- `Proof-checking invocations` counts `rocq_check`, `rocq_compile_file`, `rocq_compile`, and shell build/proof commands.
- `Shell read/inspection commands` is a heuristic category for commands such as `sed`, `cat`, `ls`, `git diff`, and `git log`; it is not directly comparable to Claude Code's dedicated Read tool.
- `File Activity` counts patch calls and references, not lines changed.

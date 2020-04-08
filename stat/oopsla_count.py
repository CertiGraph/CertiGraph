import re
import sys


def get_file_names(list_file_name: str):
    f = open(list_file_name, 'r')
    lines = [i.strip(' \t\n\r') for i in f.readlines()]
    f.close()
    return lines


thm_pattern = re.compile(r" *(Lemma|Theorem|Corollary|Remark|Fact|"
                         r"Proposition) +")


def_pattern = re.compile(r" *(Program Definition|Definition|Fixpoint|"
                         r"Inductive|Class) +")


def count_patterns(coq_file_name: str, pattern: re.Pattern) -> int:
    f = open(coq_file_name, 'r')
    total = 0
    for line in f:
        m = pattern.match(line)
        if m:
            total += 1
    f.close()
    return total


def count_lines(coq_file_name: str) -> int:
    with open(coq_file_name) as f:
        for i, l in enumerate(f):
            pass
    return i + 1


def main(argv):
    prefix = argv[1]
    coq_files = get_file_names(argv[2])
    total_lines = 0
    total_theorems = 0
    total_definitions = 0
    for name in coq_files:
        total_lines += count_lines(prefix + name)
        total_definitions += count_patterns(prefix + name, def_pattern)
        total_theorems += count_patterns(prefix + name, thm_pattern)
    print(argv[2], len(coq_files), total_lines, total_definitions,
          total_theorems, sep=' & ', end=' \\\\\n')


if __name__ == "__main__":
    main(sys.argv)

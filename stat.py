import re

coq_file_names = 'RamifyFiles.txt'


def get_file_names(list_file_name: str):
    f = open(list_file_name, 'r')
    lines = [i.strip(' \t\n\r') for i in f.readlines()]
    f.close()
    return lines


thm_pattern = re.compile(r" *(Lemma|Theorem|Corollary|Remark|Fact|Proposition)"
                         r" +([a-zA-Z][a-zA-Z0-9_']*).*")


def_pattern = re.compile(r" *(Program Definition|Definition|Fixpoint|"
                         r"Inductive|Class) +([a-zA-Z][a-zA-Z0-9_']*).*")


def get_def_or_thm(coq_file_name: str, pattern: re.Pattern):
    f = open(coq_file_name, 'r')
    names = []
    for line in f:
        m = pattern.match(line)
        if m:
            names.append(m.group(2))
    f.close()
    return names


def flatten(l: list):
    return [item for sublist in l for item in sublist]


all_thms = flatten([get_def_or_thm(f_name, thm_pattern) for f_name in
                    get_file_names(coq_file_names)])

all_defs = flatten([get_def_or_thm(f_name, def_pattern) for f_name in
                    get_file_names(coq_file_names)])


def repeated_items(l: list):
    return set([x for x in l if l.count(x) > 1])


def gen_def_or_thm_insert(file_name: str, pat: re.Pattern, tbl_name: str):
    f = open(file_name, 'w')
    for name in get_file_names(coq_file_names):
        dirname = name.split('/')
        dir = dirname[0]
        src = dirname[1]
        for def_or_thm in get_def_or_thm(name, pat):
            f.write("insert into " + tbl_name + " values (\""
                    + def_or_thm + "\", \"" + dir + "\", \"" + src + "\");\n")
    f.close()


nonid_pattern = re.compile(r"[^a-zA-Z0-9_']")


def gen_occur_insert(file_name: str, pat: re.Pattern,
                     tbl_name: str, items: list):
    f = open(file_name, 'w')
    nodup_items = set(items)
    for name in get_file_names(coq_file_names):
        dirname = name.split('/')
        dir = dirname[0]
        src = dirname[1]
        rfile = open(name, 'r')
        soup = flatten([nonid_pattern.split(line)
                        for line in rfile.readlines()])
        rfile.close()
        for item in nodup_items:
            count = soup.count(item)
            if count > 0:
                f.write('insert into ' + tbl_name + ' values ("'
                        + item + '", "' + dir + '", "' + src + '", '
                        + str(count) + ');\n')
    f.close()


def create_insert_sql():
    gen_def_or_thm_insert("insert_def.sql", def_pattern, "def")
    gen_def_or_thm_insert("insert_thm.sql", thm_pattern, "thm")
    gen_occur_insert("insert_def_occur.sql", def_pattern,
                     "def_occur", all_defs)
    gen_occur_insert("insert_thm_occur.sql", thm_pattern,
                     "thm_occur", all_thms)

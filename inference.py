import sys


def main():
    text_file = open("input.txt", "r")
    output_file = open('output.txt', 'w')
    queries = read_queries(text_file)
    kb = read_kb(text_file)
    for q in queries:
        try:
            rs = bc_ask(kb, q)
        except:
            rs = "FALSE"
        print q + " " + rs
        output_file.write(rs+"\n")


FAILURE = "failure"
TRUE = "True"
tracker = {}


def bc_ask(kb, query):
    s = {}
    tracker.clear()
    sl = bc_or(kb, query, s)
    for k in sl:
        if FAILURE in k:
            continue
        elif TRUE in k and FAILURE not in k:
            return "TRUE"
    return "FALSE"


def bc_or(kb, goal, subst):
    op = get_op(goal)
    flag = 0
    lists = []
    if goal in tracker:
        subst[FAILURE] = FAILURE
        lists.append(subst)
        return lists
    if is_fact(goal):
        tracker[goal] = TRUE
    if goal in kb and TRUE in kb[goal]:
        subst[TRUE] = TRUE
        tracker.pop(goal, None)
        lists.append(subst)
        return lists
    # Fetch all the rules for the given query
    rules = {k: v for k, v in kb.items() if op == get_op(k)}
    for rhs, lhs in rules.items():
        flag = 1
        for l in lhs:
            temp_subs = {}
            if l != TRUE:
                unify(rhs, goal, temp_subs)
                bc_and(kb, l, temp_subs)
            else:
                unify(rhs, goal, temp_subs)
                bc_and(kb, goal, temp_subs)
            if FAILURE not in temp_subs and TRUE in temp_subs:
                tracker.pop(goal, None)
                temp_subs.update(subst)  # Need to standardize variables here
                lists.append(temp_subs)
    if flag == 0 or not lists:
        subst[FAILURE] = FAILURE
        lists.append(subst)
    return lists


def bc_and(kb, goals, sl):
    if sl and FAILURE in sl:
        return sl
    elif len(goals) == 0:
        return sl
    else:
        gl = goals.split("^")
        first = gl[0]
        gl.remove(first)
        rest = "^".join(gl)
        v = dict.copy(sl)
        first = subst(first, sl)
        # tracker[first] = TRUE
        res_l = bc_or(kb, first, sl)
        f = 1
        for s in res_l:
            if rest and FAILURE not in s:
                bc_and(kb, rest, s)
            if FAILURE not in s and TRUE in s:
                sl.update(s)
                f = 0
        if f == 1:
            sl[FAILURE] = FAILURE
        return sl


def unify(x, y, subst):
    if subst:
        if FAILURE in subst:
            return subst
    if x == y:
        return subst
    if is_variable(x):
        unify_var(x, y, subst)
    elif is_variable(y):
        unify_var(y, x, subst)
    elif is_compound(x) and is_compound(y):
        unify(get_op(x), get_op(y), subst)
        return unify(get_args(x), get_args(y), subst)
    elif is_list(x) and is_list(y):
        first_a, rest_a = split_list(x)
        first_b, rest_b = split_list(y)
        unify(first_a, first_b, subst)
        return unify(rest_a, rest_b, subst)
    else:
        subst[FAILURE] = FAILURE
        return subst


def unify_var(var, x, subst):
    # if is_variable(x) and is_variable(var):
    #     return subst
    if var in subst.keys():
        return unify(subst[var], x, subst)
    elif occur_check(var, x, subst):
        subst[FAILURE] = FAILURE
    else:
        x = substitute(x, subst)
        subst[var] = x


def occur_check(var, x, s):
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return occur_check(var, s[x], s)
    elif is_compound(x):
        return (occur_check(var, get_op(x), s) or
                occur_check(var, get_args(x), s))
    else:
        return False


def is_compound(x):
    if "(" in x:
        return True
    else:
        return False


def get_args(a):
    if is_compound(a):
        return a[a.find("(")+1:len(a)-1]  # get the string between parenthesis


def get_op(a):
    return a[0:a.find("(")]


def is_list(x):
    if "," in x:
        return True


def split_list(x):
    if "(" in x[0:x.find(",")]:
        return x[0:x.find(")")+1], x[x.find(")")+2:len(x)]
    else:
        return x[0:x.find(",")], x[x.find(",")+1:len(x)]


def is_variable(x):
    if x.islower() and not is_list(x) and not is_compound(x):
        return True
    else:
        return False


def is_fact(goal):
    for i in get_args(goal).split(","):
        if is_variable(i):
            return False
    return True


def get_variable(str_args):
    args = str_args.split(",")
    for arg in args:
        if not is_variable(arg):
            args.remove(arg)
    return args


def subst(sentance, slist):
    args = get_args(sentance).split(',')
    for a in args:
        if is_compound(a):
            subst(sentance, slist)
        elif is_variable(a):
            if a in slist.keys():
                substitution_value = slist[a]
                if is_variable(substitution_value) and substitution_value in slist:
                    substitution_value = slist[substitution_value]
                for n, i in enumerate(args):
                    if i == a:
                        args[n] = substitution_value
                sentance = get_op(sentance) + '(' + ','.join(args) + ')'
    return sentance


def substitute(statement, subst):
    if is_compound(statement):
        for i in get_variable(get_args(statement)):
            if i in subst.keys():
                statement = replace_var_val(statement, i, subst[i])
    return statement


def replace_var_val(x, var, val):
    if is_compound(x):
        u_arg = []
        for arg in get_args(x).split(","):
            if is_variable(arg) and arg == var:
                u_arg.append(val)
            elif is_compound(arg):
                u_arg.append(replace_var_val(arg, var, val))
            else:
                u_arg.append(arg)
        x = get_op(x)+"("+",".join(u_arg)+")"
    return x


# Reading the input file
def read_queries(text_file):
    queries = []
    for i in range(int(text_file.readline())):
        queries.append(text_file.readline().strip())
    return queries


def read_kb(text_file):
    kb = {}
    for i in range(int(text_file.readline())):
        st = text_file.readline().strip()
        st = st.replace(" ", "")
        if ">" in st:
            st.split(">")
            k = st[st.find(">")+1:len(st)]
            v = st[0:st.find(">")-1]
            keys = standardize(k, i)
            t = []
            for c in v.split("^"):
                t.append(standardize(c, i))
            values = "^".join(t)
            kb.setdefault(keys, []).append(values)
        else:
            key = st[0:st.find(")")+1]
            value = TRUE
            kb.setdefault(key, []).append(value)
    return kb


def standardize(clause, i):
    l = []
    args = get_args(clause).split(",")
    for v in args:
        if is_variable(v):
            l.append(v + str(i))
        else:
            l.append(v)
    clause = get_op(clause) + "("+",".join(l)+")"
    return clause


main()

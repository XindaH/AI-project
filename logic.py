# Xinda Huang xhv2881/ Guanglong Xu gxo2990
import read,global_list


class Statement(object):
    def __init__(self, pattern):
        self.full = pattern
        self.predicate = pattern[0].upper()
        self.args = pattern[1:]
        self.facts = []
        self.rules = []

    def pretty(self):
        return "(" + ' '.join(self.full) + ")"

    def add_fact(self, fact1):
        self.facts.append(fact1)

    def add_rule(self, rule):
        self.rules.append(rule)


class Rule(object):
    count = 0

    def __init__(self, lhs, rhs):
        self.full = lhs + rhs
        self.type = "Assert"
        self.name = "Rule " + str(Rule.count)
        self.lhs = map(lambda (x): Statement(x), lhs)
        if rhs[0][0] == "~":
            rhs[0] = rhs[0][1:]
            self.type = "Retract"
        self.rhs = Statement(rhs)
        self.facts = []
        self.rules = []
        Rule.count = Rule.count + 1

    def pretty(self):
        return str(self.name) + ": When <" + " ".join(map(lambda x: x.pretty(), self.lhs)) + "> " + str(
            self.type) + " " + str(self.rhs.pretty())

    def add_fact(self, fact):
        self.facts.append(fact)

    def add_rule(self, rule):
        self.rules.append(rule)


def match(pattern, fact):
    p = pattern.full
    f = fact.full
    if p[0] != f[0]:
        return False
    return match_args(p[1:], f[1:])


def match_args(pattern_args, fact_args):
    bindings = {}
    # print(pattern_args, fact_args)
    for p, f in zip(pattern_args, fact_args):
        bindings = match_element(p, f, bindings)
        if False == bindings:
            return False
    return bindings


def match_element(p, f, bindings):
    # print(p, f, bindings)
    if p == f:
        return bindings
    elif var(p):
        bound = bindings.get(p, False)
        if bound:
            if f == bound:
                return bindings
            else:
                return False
        else:
            bindings[p] = f
            return bindings
    else:
        return False


def instantiate(pattern, bindings):
    predicate = pattern[0]
    args = map(lambda x: bindings.get(x, x), pattern[1:])
    args.insert(0, predicate)
    return args


def var(item):
    if item[0] == "?":
        return True
    else:
        return False


#############################knowledge base###############################
class kb:
    def __init__(self):

        facts, rules = read.read_tokenize("statements.txt")

        for fact in facts:
            assert_fact(Statement(fact))
        for new_rule in rules:
            assert_rule(Rule(new_rule[0], new_rule[1]))


def assert_fact(fact):
    temp_kb = []
    for f in global_list.KB:
        temp_kb.append(f.full)
    if fact.full not in temp_kb:
        global_list.KB.append(fact)
        infer_from_fact(fact)


def assert_rule(rule):
    temp_rb = []
    for r in global_list.RB:
        temp_rb.append(r.full)
    if rule.full not in temp_rb:
        global_list.RB.append(rule)
        infer_from_rule(rule)


def infer_from_fact(fact):
    for r in global_list.RB:
        bindings = match(r.lhs[0], fact)
        if bindings:
            if r.type == "Assert":
                if len(r.lhs) == 1:
                    new_statement = Statement(instantiate(r.rhs.full, bindings))
                    fact.add_fact(new_statement)
                    r.add_fact(new_statement)  # change add_rule to add_fact
                    assert_fact(new_statement)
                else:
                    tests = map(lambda x: instantiate(x.full, bindings), r.lhs[1:])
                    rhs = instantiate(r.rhs.full, bindings)
                    new_rule = Rule(tests, rhs)
                    r.add_rule(new_rule)
                    fact.add_rule(new_rule)
                    assert_rule(new_rule)
            if r.type == "Retract":
                new_statement = Statement(instantiate(r.rhs.full, bindings))
                fact.add_fact(new_statement)
                for ff in fact.facts:
                    delete(ff)
                for rr in fact.rules:
                    delete(rr)


def infer_from_rule(rule):
    for f in global_list.KB:
        bindings = match(rule.lhs[0], f)
        if bindings:
            if rule.type == "Assert":
                if len(rule.lhs) == 1:
                    new_statement = Statement(instantiate(rule.rhs.full, bindings))
                    rule.add_fact(new_statement)
                    f.add_fact(new_statement)
                    assert_fact(new_statement)
                else:
                    tests = map(lambda x: instantiate(x.full, bindings), rule.lhs[1:])
                    rhs = instantiate(rule.rhs.full, bindings)
                    new_rule = Rule(tests, rhs)
                    rule.add_rule(new_rule)
                    f.add_rule(new_rule)
                    assert_rule(new_rule)

            if rule.type == "Retract":
                new_statement = Statement(instantiate(rule.rhs.full, bindings))
                f.add_fact(new_statement)
                for ff in f.facts:
                    delete(ff)
                for rr in f.rules:
                    delete(rr)


def delete(factorrule):
    temp = []
    for fact_temp in global_list.KB:
        if factorrule.full == fact_temp.full:
            print 'delete the fact: ' + fact_temp.pretty()
            temp.append(fact_temp)
            global_list.KB.remove(fact_temp)
    for rule_temp in global_list.RB:
        if rule_temp.full == factorrule.full:
            print 'delete the rule: ' + rule_temp.pretty()
            temp.append(rule_temp)
            global_list.RB.remove(rule_temp)

    for insf in temp:
        for s in insf.facts:
            print 'Relevant facts(support): ' + s.pretty()
            delete(s)
    for insr in temp:
        for s in insr.rules:
            print 'Relevant rules(support): ' + s.pretty()
            delete(s)
    return


def ask(pattern, flag):
    result = []
    list_of_bindings_lists = []
    for fact in global_list.KB:
        bindings = match(Statement(pattern), fact)
        if bindings and not (bindings in list_of_bindings_lists):
            list_of_bindings_lists.append(bindings)
            if flag == 1:
                print "Asking " + Statement(pattern).pretty()
                print "This is true: \t",
                print Statement(instantiate(pattern, bindings)).pretty()
            result.append(Statement(instantiate(pattern, bindings)))
    if len(list_of_bindings_lists) == 0:
        if flag == 1:
            print 'No matching solutions \n'
    return result


def retract(pattern):
    fact = Statement(pattern)
    delete(fact)


def ask_plus(patterns):
    bindings_lists = []
    for pattern in patterns:
        if bindings_lists != []:
            for pair in map(lambda b: (instantiate(pattern, b), b), bindings_lists):
                for fact in global_list.KB:
                    bindings = match(Statement(pair[0]), fact)
                    if bindings != False:
                        for key in pair[1]:
                            bindings[key] = pair[1][key]
                        bindings_lists.append(bindings)
        else:
            for fact in global_list.KB:
                bindings = match(Statement(pattern), fact)
                if bindings != False:
                    bindings_lists.append(bindings)
    a = {}
    for bi in bindings_lists:
        if bindings_lists.count(bi) > 1:
            a[bi.get(key)] = bindings_lists.count(bi)

    bindings_lists_new = []
    for ai in a:
        temp = {}
        temp[key] = ai
        bindings_lists_new.append(temp)

    return bindings_lists_new


# judge whether fact in KB. If not, return false; If yes, get all the facts and rules support the fact.
def why(fact_why):
    result = []
    que = []
    # fact_why = Statement(fact_why)
    temp_kb = []
    for f in global_list.KB:
        temp_kb.append(f.full)

    if fact_why.full not in temp_kb:
        print 'Fact:' + str(fact_why.pretty()) + ' not in Knowledge Base and there is no facts/rules to support it \n'
    else:
        que.append(fact_why)
        while len(que) > 0:
            temp = que.pop()
            flag = False
            for f in global_list.KB:
                for fts in f.facts:
                    if temp.full == fts.full:
                        que.append(f)
                        flag = True
                for rls in f.rules:
                    if temp.full == rls.full:
                        que.append(f)
                        flag = True
            for r in global_list.RB:
                for fts in r.facts:
                    if temp.full == fts.full:
                        que.append(r)
                        flag = True
                for rls in r.rules:
                    if temp.full == rls.full:
                        que.append(r)
                        flag = True
            if flag is not True:
                result.append(temp.pretty())
        print "fact: " + str(fact_why.pretty()) + "\n"
        print "This fact is true and it is supported by: \n"
        print result
        print "\nasserted!"
        print "\n"

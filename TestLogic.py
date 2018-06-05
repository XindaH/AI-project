import read, logic, global_list

# This file tests the functions that are accessible through the command line:
# 
# You will need to wrap these functions around whatever you have written. The assumption
# is that you have each of these already written.
#
# This file assumes that you have a class "kb" for your knowledge base
#
# You need to have your code in the file logic.py
#
# For your testing, this file plus the three data files (asserts.txt, retracts.txt, and 
# ask.txt) all have to be in the same folder.
#
# This file directly tests the following:
#
# ASSERT (here called KB_assert. It take either a statement or a rule and 
# adds them to the knowledge base. It then checks to see if there are any inferences
# based on existing rules and facts that can be made.
#
# ASK (here called KB_ask). It takes a statement and returns a list of bindings that
# can be used to instantiate that pattern.
#
# INSTANTIATE (here called instantiate) that takes a pattern and a set of bindings
# and builds a new, complete statement 
#
# RETRACT (here called KB_retract) that takes a statement (not a rule) and removes 
# it from the knowledge base and then removes all facts and rules that it might support.
#
# WHY (here called KB_why) that takes a statement, finds facts that match it and then maps
# out the facts and rules that support it.
#
# ASK+ (here called KB_ask_plus) that takes a list of statements and returns the lists 
# of the various bindings that have to hold for those statements to be true in the data. 
#
# The test file also displays the instantiated list of input statements instantiated with
# the each of the bindings that were found


print "\033[0;32m\n=================== Loading in the data ===================\x1b[0m"

facts, rules = read.read_tokenize("asserts.txt")

retracts, retract_rules = read.read_tokenize("retracts.txt")

asks, ask_rules = read.read_tokenize("asks.txt")

print "\033[0;32m\n=================== Setting up the Knowledge Base ===================\x1b[0m"

ins = logic.kb()

print
print "KB: # of facts " + str(len(global_list.KB)) +" # of rules "+ str(len(global_list.RB))
for kb in global_list.KB:
    print "fact: " + kb.pretty()
for rb in global_list.RB:
    print rb.pretty()
print

print "\033[0;32m\n=================== Testing KB_Assert ===================\x1b[0m"

for rule in rules:
    logic.assert_rule(logic.Rule(rule[0], rule[1]))

for fact in facts:
    logic.assert_fact(logic.Statement(fact))

for fact in global_list.KB:
    print "fact: " + fact.pretty()

print "\033[0;32m\n=================== Testing KB_ask ===================\x1b[0m"

for ask in asks:
    print "\nAsking : " + str(ask)
    matches = logic.ask(ask, 1)
    if len(matches) == 0:
        print "No matches in KB"
    else:
        for match in logic.ask(ask, 1):
            print match,
        print

print "\033[0;32m\n=================== Testing KB_ask and instantiate ===================\x1b[0m"

for ask in asks:
    print "\nAsking : " + str(ask)
    matches = logic.ask(ask, 1)
    if len(matches) == 0:
        print "No matches in KB"
    else:
        print "Found:",
        # for match in logic.ask(kbase, ask,1):
        #     print logic.instantiate(ask, match),
        print

print "\033[0;32m\n=================== Testing retract ===================\x1b[0m"

print
print kb

logic.retract(["color", "bigbox", "red"])

logic.retract(["size", "bigbox", "big"])

print kb

print "\033[0;32m\n=================== Asserting what we just retracted ===================\x1b[0m"

logic.assert_fact(logic.Statement(["color", "bigbox", "red"]))

logic.assert_fact(logic.Statement(["size", "bigbox", "big"]))

print
for kb in global_list.KB:
    print "fact: " + kb.pretty()
for rb in global_list.RB:
    print rb.pretty()
print

print "\033[0;32m\n=================== Testing against Why ===================\x1b[0m"

for fact in global_list.KB:
    logic.why(fact)

print "\033[0;32m\n=================== Testing against Ask PLus ===================\x1b[0m"

statement_list1 = [["color", "?y", "red"], ["color", "?x", "green"]]
statement_list2 = [["color", "?y", "?x"], ["inst", "?y", "box"], ["size", "?y", "?z"]]

print "\nAsking about: " + str(statement_list1)

list_of_bindings = logic.ask_plus(statement_list1)

print "Found " + str(len(list_of_bindings)) + " sets of bindings"

for b in list_of_bindings:
    print 'This is True: '
    for pattern in statement_list1:
        print logic.Statement(logic.instantiate(pattern, b)).pretty()
if len(list_of_bindings) == 0:
    print 'No matching solutions \n'

print "\nAsking about: " + str(statement_list2)

list_of_bindings = logic.ask_plus(statement_list2)

print "Found " + str(len(list_of_bindings)) + " sets of bindings"

for b in list_of_bindings:
    print 'This is True: '
    for pattern in statement_list2:
        print logic.Statement(logic.instantiate(pattern, b)).pretty()
if len(list_of_bindings) == 0:
    print 'No matching solutions \n'

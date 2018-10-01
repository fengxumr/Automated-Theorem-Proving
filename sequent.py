import re, sys

def sep_sequent(string):
    a, b = [i.strip().strip('[').strip(']') for i in string.split('seq')]
    return [[[i.strip() for i in a.split(',') if i != ''], [i.strip() for i in b.split(',') if i != '']]]

def sep_formulae(formula):
    formula_list = [i for i in formula]
    con = []
    temp = ''
    par = 0;
    while formula_list:
        m = formula_list.pop(0)
        if m == '(':
            par += 1
            temp += m
        elif m == ')':
            par -= 1
            temp += m
            if par == 0:
                con.append(temp[1:-1])
                temp = ''
        else:
            if par != 0:
                temp += m
            else:
                if m == ' ':
                    if temp != '':
                        con.append(temp)
                        temp = ''
                else:
                    temp += m
                    if formula_list == []:
                        con.append(temp)
    return con

def rule_p2a_p2b(list_all_pairs, proof):
    for seq in list_all_pairs:
        list_l, list_r = seq
        while any(['neg' in sep_formulae(m) for m in list_l + list_r]):
            for i, elem in enumerate(list_l):
                if 'neg' in sep_formulae(elem):
                    list_l.pop(i)
                    list_r.append(sep_formulae(elem)[1])
                    # print('Rule P2a:')
                    proof.append('\nRule P2a:')
                    print_list(list_all_pairs, proof)
                    break
            for i, elem in enumerate(list_r):
                if 'neg' in sep_formulae(elem):
                    list_r.pop(i)
                    list_l.append(sep_formulae(elem)[1])
                    # print('Rule P2b:')
                    proof.append('\nRule P2b:')
                    print_list(list_all_pairs, proof)
                    break

def rule_p3a(list_all_pairs, proof):
    while any(['and' in sep_formulae(n) for m in list_all_pairs for n in m[1]]):
        for k, seq in enumerate(list_all_pairs):
            flag = 0
            list_l, list_r = seq
            for i, elem in enumerate(list_r):
                if 'and' in sep_formulae(elem):
                    list_all_pairs.pop(k)
                    list_all_pairs.append([list_l, list_r[:i] + [sep_formulae(elem)[0]] + list_r[i+1:]])
                    list_all_pairs.append([list_l, list_r[:i] + [sep_formulae(elem)[2]] + list_r[i+1:]])
                    flag = 1
                    # print('Rule P3a:')
                    proof.append('\nRule P3a:')
                    print_list(list_all_pairs, proof)
                    break
            if flag == 1:
                break

def rule_p3b_p4a(list_all_pairs, proof):
    for seq in list_all_pairs:
        list_l, list_r = seq
        while any(['and' in sep_formulae(m) for m in list_l]):
            for i, elem in enumerate(list_l):
                if 'and' in sep_formulae(elem):
                    list_l.pop(i)
                    list_l.extend([a for a in sep_formulae(elem) if a != 'and'])
                    # print('Rule P3b:')
                    proof.append('\nRule P3b:')
                    print_list(list_all_pairs, proof)
                    break
        while any(['or' in sep_formulae(m) for m in list_r]):
            for i, elem in enumerate(list_r):
                if 'or' in sep_formulae(elem):
                    list_r.pop(i)
                    list_r.extend([a for a in sep_formulae(elem) if a != 'or'])
                    # print('Rule P4a:')
                    proof.append('\nRule P4a:')
                    print_list(list_all_pairs, proof)
                    break

def rule_p4b(list_all_pairs, proof):
    while any(['or' in sep_formulae(n) for m in list_all_pairs for n in m[0]]):
        for k, seq in enumerate(list_all_pairs):
            flag = 0
            list_l, list_r = seq
            for i, elem in enumerate(list_l):
                if 'or' in sep_formulae(elem):
                    list_all_pairs.pop(k)
                    list_all_pairs.append([list_l[:i] + [sep_formulae(elem)[0]] + list_l[i+1:], list_r])
                    list_all_pairs.append([list_l[:i] + [sep_formulae(elem)[2]] + list_l[i+1:], list_r])
                    # print('Rule P4b:')
                    proof.append('\nRule P4b:')
                    print_list(list_all_pairs, proof)
                    flag = 1
                    break
            if flag == 1:
                break

def rule_p5a(list_all_pairs, proof):
    for seq in list_all_pairs:
        list_l, list_r = seq
        if any(['imp' in sep_formulae(m) for m in list_r]):
            for i, elem in enumerate(list_r):
                if 'imp' in sep_formulae(elem):
                    list_r[i] = sep_formulae(elem)[2]
                    list_l.append(sep_formulae(elem)[0])
                    # print('Rule P5a:')
                    proof.append('\nRule P5a:')
                    print_list(list_all_pairs, proof)

def rule_p5b(list_all_pairs, proof):
    while any(['imp' in sep_formulae(n) for m in list_all_pairs for n in m[0]]):
        for k, seq in enumerate(list_all_pairs):
            flag = 0
            list_l, list_r = seq
            for i, elem in enumerate(list_l):
                if 'imp' in sep_formulae(elem):
                    list_all_pairs.pop(k)
                    list_all_pairs.append([list_l[:i] + [sep_formulae(elem)[2]] + list_l[i+1:], list_r])
                    list_all_pairs.append([list_l[:i] + list_l[i+1:], list_r + [sep_formulae(elem)[0]]])
                    # print('Rule P5b:')
                    proof.append('\nRule P5b:')
                    print_list(list_all_pairs, proof)
                    flag = 1
                    break
            if flag == 1:
                break

def rule_p6a(list_all_pairs, proof):
    while any(['iff' in sep_formulae(n) for m in list_all_pairs for n in m[1]]):
        for k, seq in enumerate(list_all_pairs):
            flag = 0
            list_l, list_r = seq
            for i, elem in enumerate(list_r):
                if 'iff' in sep_formulae(elem):
                    list_all_pairs.pop(k)
                    list_all_pairs.append([list_l + [sep_formulae(elem)[0]], list_r[:i] + [sep_formulae(elem)[2]] + list_r[i+1:]])
                    list_all_pairs.append([list_l + [sep_formulae(elem)[2]], list_r[:i] + [sep_formulae(elem)[0]] + list_r[i+1:]])
                    # print('Rule P6a:')
                    proof.append('\nRule P6a:')
                    print_list(list_all_pairs, proof)
                    flag = 1
                    break
            if flag == 1:
                break

def rule_p6b(list_all_pairs, proof):
    while any(['iff' in sep_formulae(n) for m in list_all_pairs for n in m[0]]):
        for k, seq in enumerate(list_all_pairs):
            flag = 0
            list_l, list_r = seq
            for i, elem in enumerate(list_l):
                if 'iff' in sep_formulae(elem):
                    list_all_pairs.pop(k)
                    list_all_pairs.append([list_l[:i] + list_l[i+1:] + [sep_formulae(elem)[0]] + [sep_formulae(elem)[2]], list_r])
                    list_all_pairs.append([list_l[:i] + list_l[i+1:], list_r + [sep_formulae(elem)[0]] + [sep_formulae(elem)[2]]])
                    # print('Rule P6b:')
                    proof.append('\nRule P6b:')
                    print_list(list_all_pairs, proof)
                    flag = 1
                    break
            if flag == 1:
                break

def print_list(list_all_pairs, proof):
    for pairs in list_all_pairs:
        string = '[' if pairs[0] else ''
        for elem in pairs[0]:
            string += elem + ', '
        string = string[:-2] + '] seq [' if string else 'seq ['
        for elem in pairs[1]:
            string += elem + ', '
        string = string[:-2] + ']'
        # print(string)
        proof.append(string)
    # proof[-1] += '\n'

######################## main ########################

string = sys.argv[1]
list_all_pairs = sep_sequent(string)

proof =[]
print_list(list_all_pairs, proof)

while True:
    if all([re.match(r'^[A-Za-z]+$', k) for m in list_all_pairs for n in m for k in n]):            # rule_p1
        result = True if all([bool(set(m[0]) & set(m[1])) for m in list_all_pairs]) else False
        print(f'The seqent is {result}.\n')
        break

    rule_p2a_p2b(list_all_pairs, proof)
    rule_p3a(list_all_pairs, proof)
    rule_p3b_p4a(list_all_pairs, proof)
    rule_p4b(list_all_pairs, proof)
    rule_p5a(list_all_pairs, proof)
    rule_p5b(list_all_pairs, proof)
    rule_p6a(list_all_pairs, proof)
    rule_p6b(list_all_pairs, proof)

if result:
    print('*' * 40)
    print('Proofs section:\n')
    print('Rule P1:')
    for p in proof[::-1]:
        print(p)
    print('\nQED.')
    print('*' * 40)


import json
import time
import subprocess
import os

clause2id, id_max = {}, 0
id2clause = {}
dic_cnf = {}
answer_literal = set([])
trival_literal = set([])
check_dic = {}
time_dic, union_size_dic = {}, {}
query_dic = {}
num_axiom = {}
start_time = time.time()


def mkdir(path):
    folder = os.path.exists(path)
    if not folder:
        os.makedirs(path)


def add_id(clause):
    global clause2id, id_max
    if clause in clause2id:
        return clause2id[clause]
    else:
        id_max += 1
        clause2id[clause] = id_max
        id2clause[id_max] = clause
        return id_max


def add_cnf(pre_ids, con_id):
    global clause2id, dic_cnf
    if con_id in dic_cnf:
        if pre_ids not in dic_cnf[con_id]:
            dic_cnf[con_id].append(pre_ids)
    else:
        dic_cnf[con_id] = [pre_ids]


def add_trival(clause, c_id):
    global trival_literal
    clause_s = clause.split(',')[-1].split('[')
    if clause_s[0][:-1] == clause_s[1][3:] or clause_s[1][3:] == "owl:Thing":
        trival_literal.add(c_id)
    return


def filter_dummy(clause):
    # Delete "Dummy(....)"
    if 'Dummy' in clause:
        clause_s = clause.replace(' Dummy(', '*').replace('Dummy(', '*').split('*')
        result = clause_s[0]
        for str_i in clause_s[1:]:
            result += str_i.split(')', 1)[1]
        assert len(clause_s) >= 2
        return result, True
    else:
        return clause, False


def load_result(file):
    global trival_literal
    with open("condor-reasoner/classification_result/{}.txt".format(file), 'r') as f:
        data = f.readlines()
        i, l = 0, len(data)
        in_clause = False
        pre_ids = []
        flag = False
        while i < l:
            line = data[i]
            clause, f = filter_dummy(line[2:-1].strip().replace('*', '').replace('+', ''))
            if f:
                flag = True

            if line[0] == 'i':
                c_id = add_id(clause)
                trival_literal.add(c_id)
                i += 1
            elif in_clause and len(line) > 2:
                c_id = add_id(clause)
                if line[0] == 'o':
                    answer_literal.add(c_id)
                    pre_ids.append(c_id)
                elif line[0] == '-':
                    add_trival(clause, c_id)
                    pre_ids.append(c_id)
                elif line[0] == '+':
                    add_cnf(tuple(sorted(pre_ids)), c_id)
                    pre_ids = []
                    in_clause = False
                i += 1
            elif line[0] == 'o' or line[0] == '-':
                in_clause = True
            else:
                i += 1

    dic_path = 'result_cnf/{}/'.format(file)
    mkdir(dic_path)
    jsobj = json.dumps(dic_cnf)
    fileObject = open(dic_path + 'cnf.json', 'w')
    fileObject.write(jsobj)
    fileObject.close()

    jsobj1 = json.dumps(clause2id)
    fileObject1 = open(dic_path + 'clause2id.json', 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()
    return flag


def write_cnf_reorder(ont_name, g):
    global dic_cnf, answer_literal
    term2new_id = {}
    ind = 0

    def renew(p):
        nonlocal term2new_id, ind
        if p in term2new_id:
            return term2new_id[p]
        else:
            ind += 1
            term2new_id[p] = ind
            return ind

    file_path = "result_cnf/{}/cnf_{}".format(ont_name, str(g))
    f = open(file_path, 'w')
    l = 0
    literal_treated = {g}
    literal_treated_history = {g}
    answer_literal_appeared = set([])
    trival_literal_appeared = set([])
    while literal_treated:
        new_literal = set([])
        for g_new in literal_treated:
            literal_treated_history.add(g_new)
            if g_new in answer_literal:
                answer_literal_appeared.add(g_new)
            elif g_new in trival_literal:
                trival_literal_appeared.add(g_new)
            else:
                if g_new not in dic_cnf:
                    print(id2clause[g_new])
                assert g_new in dic_cnf
                for s in dic_cnf[g_new]:
                    for p in s:
                        f.write('-' + str(renew(p)) + ' ')
                        if p not in literal_treated_history:
                            new_literal.add(p)
                    f.write(str(renew(g_new)) + ' 0\n')
                    l += 1
        literal_treated = new_literal
    l_s = l
    for a in answer_literal_appeared:
        f.write(str(renew(a)) + ' 0\n')
        l += 1
    l_e = l

    for a in trival_literal_appeared:
        f.write(str(renew(a)) + ' 0\n')
        l += 1

    f.write('-' + str(renew(g)) + ' 0\n')
    f.close()
    return file_path, l_s, l_e, l


def write_cnf(ont_name, g):
    global dic_cnf, answer_literal

    file_path = "result_cnf/{}/cnf_{}".format(ont_name, str(g))
    f = open(file_path, 'w')
    l = 0
    literal_treated = {g}
    literal_treated_history = {g}
    answer_literal_appeared = set([])
    trival_literal_appeared = set([])
    while literal_treated:
        new_literal = set([])
        for g_new in literal_treated:
            literal_treated_history.add(g_new)
            if g_new in answer_literal:
                answer_literal_appeared.add(g_new)
            elif g_new in trival_literal:
                trival_literal_appeared.add(g_new)
            else:
                if g_new not in dic_cnf:
                    print(id2clause[g_new])
                assert g_new in dic_cnf
                for s in dic_cnf[g_new]:
                    for p in s:
                        f.write('-' + str(p) + ' ')
                        # f.write(id2clause[p] + "\n")
                        if p not in literal_treated_history:
                            new_literal.add(p)
                    f.write(str(g_new) + ' 0\n')
                    # f.write("__________+:  "+id2clause[g_new] + "\n\n")
                    l += 1
        literal_treated = new_literal
    l_s = l
    for a in answer_literal_appeared:
        f.write(str(a) + ' 0\n')
        # f.write(id2clause[a] + "\n\n")
        l += 1
    l_e = l

    for a in trival_literal_appeared:
        f.write(str(a) + ' 0\n')
        # f.write(id2clause[a] + "\n\n")
        l += 1

    f.write('-' + str(g) + ' 0\n')
    # f.write(id2clause[g] + "\n\n")
    f.close()
    return file_path, l_s, l_e, l


def check(k):
    global check_dic
    if k in check_dic:
        return check_dic[k]
    elif k not in dic_cnf:
        print(k, id2clause[k])
    for l in dic_cnf[k]:
        for e in l:
            if e in answer_literal or e in trival_literal or e == k:
                continue
            if not check(e):
                break
        else:
            check_dic[k] = True
            return True

    check_dic[k] = False
    return False


def get_clause(i, file):
    with open(file, 'r') as f:
        result = f.readlines()[i]
    id = result.split(' ')[0]
    clause = id2clause[int(id)]
    return clause


# @profile
def cal_single_turn(cnf_path, l_s, l_e):
    union_size = 0
    time_cost = 0
    for i in range(l_s, l_e):
        cmd = './cmmus -i result_cnf/queries/{} {}'.format(i, cnf_path)
        s_t = time.time()
        process = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   shell=True)
        try:
            output, unused_err = process.communicate(timeout=10)
        except Exception:
            process.kill()
            return 'False', 0
        time_cost += time.time() - s_t

        output = output.decode("utf-8").split('\n')
        if len(output) > 8:
            union_size += 1
            # print(get_clause(i, cnf_path))
    return time_cost, union_size


def cal(ont_name, g):
    s_t = time.time()
    cnf_path, l_s, l_e, l = write_cnf(ont_name, g)
    write_cnf_time = time.time() - s_t
    # print('num axioms(for this pair):', l_e-l_s, l_s, l_e)
    for i in range(l_s, l_e):
        dirs = 'result_cnf/queries/{}'.format(i)
        if not os.path.exists(dirs):
            with open(dirs, 'w') as f1:
                f1.write(str(i))

    time_cost, union_size = cal_single_turn(cnf_path, l_s, l_e)
    return write_cnf_time, time_cost, union_size, l_s, l_e, l


import time
from sys import argv
import os


def main_trival(ont_name, query):
    global clause2id, id_max, id2clause, dic_cnf, answer_literal, trival_literal, check_dic

    flag = load_result(ont_name)
    if flag:
        print('--------{}--------contain Dummy(...), passed!!\n'.format(ont_name))
        return

    ax = query.split('(', 1)[1][:-1]
    subsumption = ax.replace(' ', ' [=  ')
    if subsumption not in clause2id:
        print('**********not inferred:', ax, ', passed!!\n')
        return

    g = clause2id[subsumption]
    write_cnf_time, time_cost, union_size, l_s, l_e, size_cnf = cal(ont_name, g)
    print(l_s, l_e)
    if not time_cost:
        print("time out!")
    else:
        print("time cost, union_size:", time_cost, union_size)

mkdir('result_cnf/queries')
mkdir('condor-reasoner/classification_result')
ont_name = argv[1]
if len(argv) <= 2:
    start_time = time.time()
    dic_ontology = 'Ontologies'
    path = dic_ontology + '/' + ont_name

    commend = 'nohup condor-reasoner/bin/condor -i {} -n >condor-reasoner/classification_result/{}.txt'.format(path,
                                                                                                               ont_name)
    os.system(commend)
    print('initialized in ', time.time() - start_time)

else:
    ont_name = argv[1]
    query_file = argv[2]
    with open(query_file, 'r') as f:
        q = f.readline()[:-1]
        main_trival(ont_name, q)

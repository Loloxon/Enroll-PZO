from datetime import timedelta
from math import floor

from minizinc import Instance, Model, Solver
from random import randint
from time import time

if __name__ == "__main__":

    # helping fuctions

    # function updating file competition_improve.dzn
    def update_data(result, new_result):
        n = len(new_result) - 1
        n1 = len(result) - 1
        if result[n1, "objective"] > new_result[n, "objective"]:
            data = open("./data/competition_improve.dzn", "r")
            list_of_lines = data.readlines()
            S = ""
            for s in new_result[n, "GroupAssignmentB"]:
                s1 = str(s)
                s1 = s1[1:-1]
                S += s1 + ", "
            S = S[:-2]
            list_of_lines[17] = "assignmentB = array2d(Student, Group, [" + S + "]);\n"
            list_of_lines[20] = "% maxObjective = " + str(new_result[n, "objective"]) + ";\n"
            a_file = open("./data/competition_improve.dzn", "w")
            a_file.writelines(list_of_lines)
            a_file.close()
            print("New solution is better (diff: ", result[n1, "objective"] - new_result[n, "objective"], "; to go: ",
                  new_result[n, "objective"]-36746,  ")", sep="")
            return new_result, True
        print("New solution is same or worse then old")
        return result, False


    # setting variables to relax s, c are number of students and classes to relax
    def get_relax_values(s, c):
        S = [1 for _ in range(174)]
        class_size = [15, 174, 15, 174, 15, 30, 174, 15, 174, 15, 174, 15, 174, 15, 174, 15, 174, 30, 174, 15, 174, 15,
                      174, 15, 174]
        C = [1 for _ in range(25)]

        for i in range(s):
            rS = randint(0, 174 - 1)
            while S[rS] == 0:
                rS = randint(0, 174 - 1)
            S[rS] = 0
        # 12 to wykłady - 13 to zajęcia
        for i in range(c):
            rC = randint(0, 25 - 1)
            while C[rC] == 0 or class_size[rC] == 174:
                rC = randint(0, 25 - 1)
            C[rC] = 0
        return S, C


    # function improving solution
    def improve_solution(instance, s, c, sec):
        S, C = get_relax_values(s, c)
        data = open("./data/competition_improve.dzn", "r")
        list_of_lines = data.readlines()
        # will be upgraded to f-string later or maybe not
        list_of_lines[18] = "relaxS = " + str(S) + ";\n"
        list_of_lines[19] = "relaxC = " + str(C) + ";\n"

        a_file = open("./data/competition_improve.dzn", "w")
        a_file.writelines(list_of_lines)
        a_file.close()

        with instance.branch() as opt:
            opt.add_file("./data/competition_improve.dzn", True)
            return opt.solve(intermediate_solutions=True, timeout=timedelta(minutes=5, seconds=sec))


    # execution starts here

    # getting op gurobi solver
    solver = Solver.lookup("gurobi")

    # setting first instance relaxing solution based on randomly chosen students or classes
    model1 = Model("models/enroll_improve.mzn")
    instance1 = Instance(solver, model1)
    # setting second instance relaxing solution based on chosen students and classes mixed
    model2 = Model("models/enroll_improve_mixed.mzn")
    instance2 = Instance(solver, model2)

    i = 0
    data = open("./data/competition_improve.dzn", "r")
    list_of_lines = data.readlines()
    print("starting objective:", int(str(list_of_lines[20])[17:-2]))
    result = {(0, "objective"): int(str(list_of_lines[20])[17:-2])}

    start_time = time()
    sec = 0
    timectr = 0
    relaxctr = 0
    studentR = 0
    classR = 5
    while True:
        checkpoint = time()
        i += 1
        # 9 grup na przedmiot
        new_result = improve_solution(instance1, studentR, classR, sec)
        tdiff = time() - checkpoint
        print("number:", i, ", students: ", studentR, ", classes", classR)
        # print("new_result", new_result[len(new_result)-2])
        # print("new_result", new_result[len(new_result)-1])
        if floor(tdiff % 60) < 10:
            print("time: ", int(tdiff // 60), ":0", floor(tdiff % 60), sep="")
        else:
            print("time: ", int(tdiff // 60), ":", floor(tdiff % 60), sep="")
        if len(new_result) > 0:
            # print("new_result:", new_result[len(new_result) - 1, "objective"])
            print(new_result[len(new_result) - 1])
            result, add = update_data(result, new_result)
            if add:
                relaxctr = 0
            else:
                relaxctr += 1
        else:
            timectr += 1
            print("Did not find any solution in given time bound")

        if relaxctr == 5:  # zwiększ relaksacje
            relaxctr = 0
            classR += 1
            studentR += 3
        if timectr == 3:  # zwiększ czas
            timectr = 0
            sec += 30
        print("relaxctr:", relaxctr, ", timectr", timectr)
        print("-------------------------------")

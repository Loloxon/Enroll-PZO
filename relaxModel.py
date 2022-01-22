from minizinc import Instance, Model, Solver
from random import randint
from time import time

if __name__ == "__main__":

    # helping fuctions
    # setting variables to relax -> will be later upgraded to chose variables more wisely not at random
    def get_relax_values(s=45, c=0):
        S = [1 for _ in range(174)]
        class_size = [15, 174, 15, 174, 15, 30, 174, 15, 174, 15, 174, 15, 174, 15, 174, 15, 174, 30, 174, 15, 174, 15,
                      174,
                      15, 174]
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


    # funcion improving solution
    def improve_solution(instance, s=3, c=0):
        S, C = get_relax_values(s, c)
        data = open("./data/competition_improve.dzn", "r")
        list_of_lines = data.readlines()
        # will be upgraded to f-string later
        list_of_lines[18] = "relaxS = " + str(S) + ";\n"
        list_of_lines[19] = "relaxC = " + str(C) + ";\n"

        a_file = open("./data/competition_improve.dzn", "w")
        a_file.writelines(list_of_lines)
        a_file.close()

        with instance.branch() as opt:
            opt.add_file("./data/competition_improve.dzn", True)
            result = opt.solve()
            return result


    def update_data(result, new_result):
        if result["objective"] > new_result["objective"]:
            data = open("./data/competition_improve.dzn", "r")
            list_of_lines = data.readlines()
            S = ""
            for s in new_result["GroupAssignmentB"]:
                s1 = str(s)
                s1 = s1[1:-1]
                S += s1 + ", "
            S = S[:-2]
            list_of_lines[17] = "assignmentB = array2d(Student, Group, [" + S + "]);\n"
            list_of_lines[20] = "maxObjective = " + str(new_result["objective"]) + ";\n"
            a_file = open("./data/competition_improve.dzn", "w")
            a_file.writelines(list_of_lines)
            a_file.close()
            print("New solution is better")
            return new_result
        print("New solution is worse or same as old")
        return result


    # execution starts here
    model = Model("./enroll_improve.mzn")

    solver = Solver.lookup("gurobi")

    instance = Instance(solver, model)

    i = 0
    result = {"objective": float('inf')}

    start_time = time()
    while True:
        checkpoint = time()
        i += 1

        classes = randint(2, 2)
        print("number: ", i)
        print("classes: ", classes, ", students: ", 70//(20*classes))
        new_result = improve_solution(instance, 70//(20*classes), classes)
        print("new_result", new_result)
        print("time: ", time() - checkpoint, "s")
        result = update_data(result, new_result)
        print("-------------------------------")


from minizinc import Instance, Model, Solver
from random import randint

if __name__ == "__main__":

    S = [1 for _ in range(174)]
    class_size = [15, 174, 15, 174, 15, 30, 174, 15, 174, 15, 174, 15, 174, 15, 174, 15, 174, 30, 174, 15, 174, 15, 174,
                  15, 174]
    C = [1 for _ in range(25)]

    for i in range(45):
        rS = randint(0, 174 - 1)
        while S[rS] == 0:
            rS = randint(0, 174 - 1)
        S[rS] = 0
    # 12 to wykłady - 13 to zajęcia
    for i in range(0):
        rC = randint(0, 25 - 1)
        while C[rC] == 0 or class_size[rC] == 174:
            rC = randint(0, 25 - 1)
        C[rC] = 0

    enroll = Model("./enroll_improve.mzn")

    gecode = Solver.lookup("gecode")

    instance = Instance(gecode, enroll)

    # data = open("./data/competition_improve.dzn", "r")
    # list_of_lines = data.readlines()
    # print(list_of_lines)
    # print(len(list_of_lines))
    # list_of_lines[21] = str(S)
    # list_of_lines[22] = str(C)

    # a_file = open("./data/competition_improve.dzn", "w")
    # a_file.writelines(list_of_lines)
    # a_file.close()

    instance.add_file("./data/competition_improve.dzn", True)

    result = instance.solve()
    for i in range(len(result)):
        print(result[i, "x"])

from random import randint

S = [1 for _ in range(174)]
class_size = [15, 174, 15, 174, 15, 30, 174, 15, 174, 15, 174, 15, 174, 15, 174, 15, 174, 30, 174, 15, 174, 15, 174, 15, 174];
C = [1 for _ in range(25)]

for i in range(10):
    rS = randint(0, 174 - 1)
    while S[rS] == 0:
        rS = randint(0, 174 - 1)
    # S[rS] = 0

for i in range(4):
    rC = randint(0, 25 - 1)
    while C[rC] == 0 or class_size[rC] == 174:
        rC = randint(0, 25 - 1)
    C[rC] = 0

print("relaxS = ", S, ";", sep="")
print("relaxC = ", C, ";", sep="")
print()
# for i in range(25):
#     if class_size[i] != 174:
#         print(C[i], class_size[i])

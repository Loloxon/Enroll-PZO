from random import randint

S = [1 for _ in range(174)]
C = [1 for _ in range(25)]

for i in range(15):
    rS = randint(0, 174 - 1)
    while S[rS] == 0:
        rS = randint(0, 174 - 1)
    S[rS] = 0

for i in range(3):
    rC = randint(0, 25 - 1)
    while S[rC] == 0:
        rC = randint(0, 25 - 1)
    C[rC] = 0

print("relaxS = ", S, ";", sep="")
print("relaxC = ", C, ";", sep="")

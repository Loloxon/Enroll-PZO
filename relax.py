from random import random, randint

S = [1 for i in range(174)]
G = [1 for i in range(127)]

for i in range(10):
    rS = randint(0,174-1);
    rG = randint(0,127-1);
    S[rS] = 0
    # G[rG] = 0
print("relaxS = ", S, ";", sep="")
print("relaxG = ", G, ";", sep="")

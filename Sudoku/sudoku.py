###################################################################
#   VUT FIT IAM DU1: Sudoku
#   Author: David Mihola (xmihol00)
#   Date: 22. 2. 2021
###################################################################

import sys

assignment = []

for line in sys.stdin:
    cell = line.split()
    if len(cell) != 3:
        exit(1)
    try:
        if int(cell[0]) > 9 or int(cell[0]) < 1 or int(cell[1]) > 9 or int(cell[1]) < 1 or int(cell[0]) > 9 or int(cell[2]) < 1:
            exit(1)

        N = int(cell[0]) * 100 + int(cell[1]) * 10 +  int(cell[2])
        assignment.append(N)
    except ValueError:
        exit(1)

print("p cnf 999", 3240 + len(assignment))

for N in assignment:
    print(N, "0")

## there is at least one number in every cell
for i in range(1, 10):
    for j in range(1, 10):
        for k in range(1, 10):
            print(str(i)+str(j)+str(k), end=" ")
        print("0")

## there is at most one number per cell
for i in range(1, 10):
    for j in range(1, 10):
        for k in range(1, 9):
            for l in range(k+1, 10):
                print("-"+str(i)+str(j)+str(k), "-"+str(i)+str(j)+str(l), 0)

## every row contains all numbers 1-9
for i in range(1, 10):
    for j in range(1, 10):
        for k in range(1, 10):
            print(str(i)+str(k)+str(j), end=" ")
        print("0")

## every column contains all numbers 1-9
for i in range(1, 10):
    for j in range(1, 10):
        for k in range(1, 10):
            print(str(k)+str(i)+str(j), end=" ")
        print("0")

## every 3x3 square contains all numbers 1-9
for i in range(0, 3):
    for j in range(0, 3):
        for k in range(1, 10):
            for l in range(1, 4):
                for m in range(1, 4):
                    print(str(3*i+l)+str(3*j+m)+str(k), end=" ")
            print("0")
    
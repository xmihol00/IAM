###################################################################
#   VUT FIT IAM DU1: 8 queens problem
#   Author: David Mihola
#   Date: 14. 2. 2021
###################################################################

import sys
import math

if len(sys.argv) != 2:
    exit(1)

try:
    N = int(sys.argv[1])
    if N <= 0:
        exit(1)
except ValueError:
    exit(1)

## calculation of the number of used formulas
formulas = 2*N*math.comb(N, 2)+2*N
for i in range(2, N+1):
    formulas += 2*math.comb(i, 2)
for i in range(2, N):
    formulas += 2*math.comb(i, 2)
print("p cnf", N*N, formulas)

## rows
for i in range(N):
    for j in range(1, N+1):
        print(N*i+j, end=" ")
    print(0)

    for j in range(1, N+1):
        for k in range(j+1, N+1):
            print(-(N*i+j), -(N*i+k), 0)

## columns
for i in range(N):
    for j in range(N):
        print(N*j+i+1, end=" ")
    print(0)

    for j in range(N):
        for k in range(j+1, N):
            print(-(N*j+i+1), -(N*k+i+1), 0)

## diagonals
for i in range(N-1):
    for j in range(i+1, N):
        for k in range(j, N):
            print(-(N*(j-1)+j-i), -(N*k+k+1-i), 0)

for i in range(N-2):
    for j in range(0, N-2):
        for k in range(j, N-2-i):
            print(-(N*j+2+j+i), -(N*(k+1)+k+3+i), 0)

for i in range(N-1):
    for j in range(i+1, N):
        for k in range(j, N):
            print(-(j*N-j+1+i), -(N*(k+1)-k+i), 0)

for i in range(N-2):
    for j in range(0, N-2):
        for k in range(j, N-2-i):
            print(-(N*(j+1)-j-1-i), -(N*(k+2)-k-2-i), 0)

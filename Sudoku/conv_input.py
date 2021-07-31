import sys

i = 1
for line in sys.stdin:
    for j in range(0,9):
        if line[j] != '0':
            print(i, j + 1, line[j])
    i += 1

import numpy as np

data = input()
data = input()

def check_sudoku(grid):
    """ Return True if grid is a valid Sudoku square, otherwise False. """
    for i in range(9):
        # j, k index top left hand corner of each 3x3 tile
        j, k = (i // 3) * 3, (i % 3) * 3
        if len(set(grid[i,:])) != 9 or len(set(grid[:,i])) != 9\
                   or len(set(grid[j:j+3, k:k+3].ravel())) != 9:
            return False
    return True

numbers = data.split()
numbers = numbers[:-1]
cells = []
for num in numbers:
    if num[0] != '-':
        cells.append(num)

sudoku = [[], [], [], [], [], [], [], [], []]
for i in range(81):
    sudoku[i % 9].append(cells[i][2:3])

print(check_sudoku(np.array(sudoku)))

#python3 conv_input.py <sudoku.txt >sudoku_conv ; python3 sudoku.py <sudoku_conv >sudoku.in ; minisat sudoku.in sudoku.out ; python3 sprint.py <sudoku.out 
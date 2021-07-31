
#=========================================================================================================
# File:        no_three_in_line.py
# Case:        VUT, FIT, IAM, DU2
# Date:        12. 3. 2021
# Author:      David Mihola
# Contact:     xmihol00@stud.fit.vutbr.cz
# Interpreted: Python 3.8.5
# Description: Script for placing points on a grid, so no three are in a straight line
# Usage:       run as: python3 no_three_in_line.py <lenght of one edge of the area> <number of points to be placed>
#==========================================================================================================

import z3
import sys
from itertools import combinations
  
if len(sys.argv) != 3:
    print("Wrong number of arguments.", file=sys.stderr)
    exit(1)

try:
    N = int(sys.argv[1])
    P = int(sys.argv[2])
except:
    print("The arguments must be integers.", file=sys.stderr)
    exit(1)

if P <= 2:
    print("There will never be 3 points on one line with this number of points.")
    exit(0)

if N <= 1:
    print("You cannot place three points in a grid of this size.\nTry it with a grid size larger than 1.")
    exit(0)

# 2 * N is the maximal number of points that can be on a grid with edge size N
if P > 2 * N:
    print("It is not possible to place more than 2 * N points on a grid of edge size N.")
    exit(0)


vars_x = [z3.Int("x%s" % (i + 1)) for i in range(P)] # x coordinates
vars_y = [z3.Int("y%s" % (i + 1)) for i in range(P)] # y coordinates

range_x = [z3.And(vars_x[i] > 0, vars_x[i] <= N) for i in range(P)] # set the range of the grid
range_y = [z3.And(vars_y[i] > 0, vars_y[i] <= N) for i in range(P)] # set the range of the grid

constrain = []
combs = list(combinations([i for i in range(P)], 3)) # find all combinations of 3 points from the total number of points
for comb in combs:
    # each combinations of points must create a triangle, otherwise these points are in a line
    constrain.append(
        # if three points create a triangle, then the area of the triangle is not 0
        vars_x[comb[0]] * (vars_y[comb[1]] - vars_y[comb[2]]) + 
        vars_x[comb[1]] * (vars_y[comb[2]] - vars_y[comb[0]]) + 
        vars_x[comb[2]] * (vars_y[comb[0]] - vars_y[comb[1]]) != 0) 

solver = z3.Solver()
solver.reset()
solver.add(constrain + range_x + range_y)
if solver.check() == z3.sat:
    model = solver.model()
    grid = [[' ' for i in range(N)] for j in range(N)]

    # print the points on the grid
    print("filled points on the grid:")
    for i in range(P):
        print('[', model[vars_x[i]], ", ", model[vars_y[i]], ']', sep='')
        grid[model[vars_y[i]].as_long() - 1][model[vars_x[i]].as_long() - 1] = '#'
    
    # print the grid
    print("The grid:")
    for i in range(N):
        for j in range(N):
            print(grid[i][j], sep='', end='')
        print()
    exit(0)


# Solutions for edge cases, it takes a while...
#  
# >$ time python3 no_three_in_line.py 5 10
# filled points on the grid:
# [4, 4]
# [3, 1]
# [2, 2]
# [5, 1]
# [4, 3]
# [5, 3]
# [1, 5]
# [1, 4]
# [2, 5]
# [3, 2]
# The grid:
#   # #
#  ##  
#    ##
# #  # 
# ##   
# 
# real    0m3,551s
# user    0m3,524s
# sys     0m0,024s

# >$ time python3 no_three_in_line.py 6 12
# filled points on the grid:
# [5, 4]
# [6, 6]
# [4, 1]
# [3, 1]
# [2, 5]
# [5, 3]
# [2, 2]
# [6, 3]
# [1, 4]
# [4, 6]
# [1, 2]
# [3, 5]
# The grid:
#   ##  
# ##    
#     ##
# #   # 
#  ##   
#    # #
# 
# real    0m12,733s
# user    0m12,641s
# sys     0m0,084s

# >$ time python3 no_three_in_line.py 7 14
# filled points on the grid:
# [2, 5]
# [1, 3]
# [5, 6]
# [3, 2]
# [3, 1]
# [4, 2]
# [2, 7]
# [6, 1]
# [4, 5]
# [7, 4]
# [6, 6]
# [5, 7]
# [7, 3]
# [1, 4]
# The grid:
#   #  # 
#   ##   
# #     #
# #     #
#  # #   
#     ## 
#  #  #  
# 
# real    0m6,807s
# user    0m6,738s
# sys     0m0,064s

# >$ time python3 no_three_in_line.py 8 16
# filled points on the grid:
# [4, 2]
# [5, 6]
# [4, 3]
# [7, 4]
# [2, 5]
# [8, 5]
# [1, 1]
# [7, 6]
# [3, 1]
# [2, 3]
# [3, 7]
# [1, 4]
# [5, 7]
# [8, 8]
# [6, 8]
# [6, 2]
# The grid:
# # #     
#    # #  
#  # #    
# #     # 
#  #     #
#     # # 
#   # #   
#      # #
# 
# real    42m20,301s
# user    42m6,985s
# sys     0m1,803s

# >$ time python3 no_three_in_line.py 9 18
# filled points on the grid:
# [3, 5]
# [7, 2]
# [3, 7]
# [1, 4]
# [8, 6]
# [4, 1]
# [5, 2]
# [4, 9]
# [5, 3]
# [2, 8]
# [8, 1]
# [7, 8]
# [2, 4]
# [1, 6]
# [9, 5]
# [6, 7]
# [6, 9]
# [9, 3]
# The grid:
#    #   # 
#     # #  
#     #   #
# ##       
#   #     #
# #      # 
#   #  #   
#  #    #  
#    # #   
# 
# real    88m27,872s
# user    88m19,110s
# sys     0m2,942s

#>$ time python3 no_three_in_line.py 10 20 
# probably still runnning...

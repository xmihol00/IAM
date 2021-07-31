
#=========================================================================================================
# File:        sudoku.py
# Case:        VUT, FIT, IAM, DU2
# Date:        4. 3. 2021
# Authors:      David Mihola - lines 32 - 45, http://www.cs.tau.ac.il/~msagiv/courses/asv/z3py/guide-examples.htm - rest
# Contact:     xmihol00@stud.fit.vutbr.cz
# Interpreted: Python 3.8.5
# Description: Script fro creating a schedul for weekly shifts of 9 workers.
#==========================================================================================================

import z3

# 9x9 matrix of integer variablesi
X = [ [ z3.Int("x_%s_%s" % (i+1, j+1)) for j in range(9) ]
      for i in range(9) ]

# each cell contains a value in {1, ..., 9}
cells_c  = [ z3.And(1 <= X[i][j], X[i][j] <= 9)
             for i in range(9) for j in range(9) ]
# each row contains a digit at most once
rows_c   = [ z3.Distinct(X[i]) for i in range(9) ]

# each column contains a digit at most once
cols_c   = [ z3.Distinct([ X[i][j] for i in range(9) ])
             for j in range(9) ]

# each 3x3 square contains a digit at most once
sq_c     = [ z3.Distinct([ X[3*i0 + i][3*j0 + j]
                        for i in range(3) for j in range(3) ])
             for i0 in range(3) for j0 in range(3) ]

# constrains for hyper sudoku
h_sq_c1  = [ z3.Distinct([ X[i][j]
                        for i in range(1, 4) for j in range(1, 4) ])]

h_sq_c2  = [ z3.Distinct([ X[i][j]
                        for i in range(5, 8) for j in range(1, 4) ])]

h_sq_c3  = [ z3.Distinct([ X[i][j]
                        for i in range(1, 4) for j in range(5, 8) ])]

h_sq_c4  = [ z3.Distinct([ X[i][j]
                        for i in range(5, 8) for j in range(5, 8) ])]

sudoku_c = cells_c + rows_c + cols_c + sq_c + h_sq_c1 + h_sq_c2 + h_sq_c3 + h_sq_c4

# sudoku instance, we use '0' for empty cells
instance = ((7,5,0,0,2,0,0,8,6),
            (0,1,8,9,0,0,5,0,0),
            (9,0,0,0,0,0,0,0,0),
            (0,0,0,0,0,0,0,9,0),
            (8,0,4,0,0,3,0,2,0),
            (0,0,0,0,0,0,3,0,0),
            (4,0,0,0,0,0,0,0,2),
            (0,0,0,0,0,7,0,0,0),
            (1,8,0,0,4,0,0,0,0))

instance_c = [ z3.If(instance[i][j] == 0,
                  True,
                  X[i][j] == instance[i][j])
               for i in range(9) for j in range(9) ]

s = z3.Solver()
s.add(sudoku_c + instance_c)
if s.check() == z3.sat:
    m = s.model()
    r = [ [ m.evaluate(X[i][j]) for j in range(9) ]
          for i in range(9) ]
    z3.print_matrix(r)
else:
    print("failed to solve")

    
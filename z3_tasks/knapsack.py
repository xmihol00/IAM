#=========================================================================================================
# File:        knapsack.py
# Case:        VUT, FIT, IAM, DU2
# Date:        13. 3. 2021
# Author:      David Mihola
# Contact:     xmihol00@stud.fit.vutbr.cz
# Interpreted: Python 3.8.5
# Description: Script solving the knapsack problem
# Usage:       run as: python3 knapsack.py <folder_name>
#              Where <folder_name> is a name of folder containing three files:
#              c.txt - capacity of the knapsack, 
#              p.txt - profits of each item seperated by new line, 
#              w.txt - weight of each item seperated by NL.
#==========================================================================================================

import z3
import sys

if len(sys.argv) != 2:
    print("Wrong number of arguments", file=sys.stderr)
    exit(1)

dir_name = sys.argv[1]

try:
    f = open(dir_name + "/c.txt", 'r')
    capacity = int(f.read())
except:
    print("File with capacity could not be opened or contains invalid data.", file=sys.stderr)
    exit(1)
finally:
    f.close

try:
    f = open(dir_name + "/w.txt", 'r')
    weights = [int(i) for i in f.read().split()]
except:
    print("File with weights could not be opened or contains invalid data.", file=sys.stderr)
    exit(1)
finally:
    f.close

try:
    f = open(dir_name + "/p.txt", 'r')
    values = [int(i) for i in f.read().split()]
except:
    print("File with values could not be opened or contains invalid data.", file=sys.stderr)
    exit(1)
finally:
    f.close

if len(values) != len(weights):
    print("The number of weightd does not correspond to the number of values.", file=sys.stderr)
    exit(1)

varaibles = [z3.Bool("x%s" % (i + 1)) for i in range(len(weights))] # create variables according to the number of items

value_constrain = values[0] * z3.If(varaibles[0], 1, 0)
for i in range(1, len(values)):
    value_constrain += values[i] * z3.If(varaibles[i], 1, 0) # create a constrain of the sum of values of all the items,
                                                             # if all of them were included.
 
weight_constrain = weights[0] * z3.If(varaibles[0], 1, 0)
for i in range(1, len(weights)):
    weight_constrain += weights[i] * z3.If(varaibles[i], 1, 0) # create a constrain of the sum of weights of all the items,
                                                               # if all of them were included

weight_constrain = weight_constrain <= capacity # add the maximal capacity to the weight constrain, 
                                                # that means some of the items cannot be included,
                                                # if the capacity is to small

max_val = sum(values)
min_val = 0

solver = z3.Solver()
model = None
while True:
    searched_val = (min_val + max_val + 1) >> 1 # change the minimal value of items in the sack using interval halving method
                                                # + 1 to make sure we do not miss a value due to an integer division
    solver.reset()
    solver.add([weight_constrain] + [value_constrain >= searched_val]) # add a contrain to a minimal value of the sack,
                                                                       # that means at least some items must be in the sack
                                                                       # to meet the value constrain

    if solver.check() == z3.sat:
        model = solver.model() # remember the last successful model
        min_val = searched_val
    else:
        max_val = searched_val
        if max_val == min_val or max_val == min_val + 1:
            break

if model != None:
    results = [1 if model[varaibles[i]] else 0 for i in range(len(varaibles))]
    for result in results:
        print(result)
        # print the result in a format from https://people.sc.fsu.edu/~jburkardt/datasets/knapsack_01/knapsack_01.html
else:
    print("Unsolvable")


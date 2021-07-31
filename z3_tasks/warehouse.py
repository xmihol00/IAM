
#=========================================================================================================
# File:        warehouse.py
# Case:        VUT, FIT, IAM, DU2
# Date:        16. 3. 2021
# Author:      David Mihola
# Contact:     xmihol00@stud.fit.vutbr.cz
# Interpreted: Python 3.8.5
# Description: Script for creating a schedul for weekly shifts of 9 workers
# Usage:       run as: python3 warehouse.py [optional switches]
#              There are 9 workers wrking in the factory, their names are:
#              Arnošt, Emil, Franta, Lojza, Marťas, Ota, Pepa, Tonda, Zdenda;
#              each worker has two switches starting with the first letter of his name
#              and followed by 's' which stands for shift or 'd' which stands for day
#              (i.e. Arnošt has switches --as and --ad, Emil has switch --es and --ed, ...).
#              By default all workers can work all shifts. But you can specify their personal
#              schedule with a value after their switches. All values are binary. Switches ending
#              with 's' are 3 bit values, switches ending with 'd' are 7 bit values.
#              1 bits in the shift switch represents that a worker can work moorning to night shifts from
#              MSB to LSB respectively. Similary 1 bits in the day switch represents that a worker can work 
#              Monday to Sunday from MSB to LSB respectively. (i.e. --as 101 --ad 1110010 --es 110; means, that
#              Arnošt can work moorning and night shifts on Monday, Tuesday, Wednesday and Saturday; 
#              Emil can work moorning and afternoon shifts on any day of the week.)
# Note:        I added a constrain that workers cannot work on a night shift followed by a morning 
#              shift the next day. Applies also to night shifts on Sundays and moorning shifts on Mondays.
#==========================================================================================================

import z3
import sys
import getopt

try:
    opts, rest = getopt.getopt(sys.argv[1:], "", 
    ["as=", "es=", "fs=", "ls=", "ms=", "os=", "ps=", "ts=", "zs=", "ad=", "ed=", "fd=", "ld=", "md=", "od=", "pd=", "td=", "zd="])
    if len(rest):
        exit(1)
except:
    print("Wrong program arguments.",
          "You can use these switches: --as, --es, --fs, --ls, --ms, --os, --ps, --ts, --zs, --ad, --ed, --fd, --ld, --md, --od, --pd, --td, --zd",
          "All of them must be followed with a binary value.", file=sys.stderr, sep='\n')
    exit(1)

# the workers
workers = ["Arnošt", "Emil", "Franta", "Lojza", "Marťas", "Ota", "Pepa", "Tonda", "Zdenda"]

# default possible shifts of each worker
workers_shifts = {"--as": 7, "--es": 7, "--fs": 7, "--ls": 7, "--ms": 7, "--os": 7, "--ps": 7, "--ts": 7, "--zs": 7}
workers_days = {"--ad": 127, "--ed": 127, "--fd": 127, "--ld": 127, "--md": 127, "--od": 127, "--pd": 127, "--td": 127, "--zd": 127}

for opt in opts:
    try:
        val = int(opt[1], base=2)
    except:
        print("Wrong program arguments.",
              "You can use these switches: --as, --es, --fs, --ls, --ms, --os, --ps, --ts, --zs, --ad, --ed, --fd, --ld, --md, --od, --pd, --td, --zd",
              "All of them must be followed with a binary value.", file=sys.stderr, sep='\n')
        exit(1)

    if opt[0].endswith('s'):
        if val < 0 or val > 7:
            print("Wrong program arguments.",
                  "You can use these switches: --as, --es, --fs, --ls, --ms, --os, --ps, --ts, --zs, --ad, --ed, --fd, --ld, --md, --od, --pd, --td, --zd",
                "All of them must be followed with a binary value.", file=sys.stderr, sep='\n')
            exit(1)

        workers_shifts[opt[0]] = val
    else:
        if val < 0 or val > 127:
            print("Wrong program arguments.",
                  "You can use these switches: --as, --es, --fs, --ls, --ms, --os, --ps, --ts, --zs, --ad, --ed, --fd, --ld, --md, --od, --pd, --td, --zd",
                "All of them must be followed with a binary value.", file=sys.stderr, sep='\n')
            exit(1)

        workers_days[opt[0]] = val


# each worker has one variable for each day in a week
vars = [z3.Int("x%s%s" % (i+1, j+1)) for i in range(7) for j in range(9)]

picky_workers = []
i = 0
for item in workers_shifts.items():
    for j in range(7):
        if not item[1] & 1: # worker does not want night shifts
            picky_workers.append(vars[j * 9 + i] != 3)
        if not item[1] & 2: # worker does not want afternoon shifts
            picky_workers.append(vars[j * 9 + i] != 2)
        if not item[1] & 4: # worker does not want moorning shifts
            picky_workers.append(vars[j * 9 + i] != 1)
    i += 1

i = 0
for item in workers_days.items():
    for j in range(6, -1, -1):
        if not item[1] & 2 ** j: # match day bits
            picky_workers.append(vars[(6 - j) * 9 + i] == 4) # worker does not want to work on a specific day
    i += 1

moornings = []
afternoons = []
nights = []
var_vals = []

for i in range(7):
    moornings.append(z3.If(vars[9 * i] == 1, 1, 0))
    afternoons.append(z3.If(vars[9 * i] == 2, 1, 0))
    nights.append(z3.If(vars[9 * i] == 3, 1, 0))
    var_vals.append(z3.If(vars[i * 9 - 9] == 3, 
                    z3.And(vars[9 * i] >= 2, vars[9 * i] <= 4),  # had a night shift the day before
                    z3.And(vars[9 * i] >= 1, vars[9 * i] <= 4))) # did not have a night shift the day before

for i in range(0, 7):
    for j in range(1, 9):
        moornings[i] += z3.If(vars[i * 9 + j] == 1, 1, 0)
        afternoons[i] += z3.If(vars[i * 9 + j] == 2, 1, 0)
        nights[i] += z3.If(vars[i * 9 + j] == 3, 1, 0)
        var_vals.append(z3.If(vars[i * 9 + j - 9] == 3, 
                              z3.And(vars[i * 9 + j] >= 2, vars[i * 9 + j] <= 4),  # had a night shift the day before
                              z3.And(vars[i * 9 + j] >= 1, vars[i * 9 + j] <= 4))) # did not have a night shift the day before
    moornings[i] = moornings[i] == 2      # there are just 2 workers on moorning shifts
    afternoons[i] = afternoons[i] == 2    # there are just 2 workers on afternoon shifts
    nights[i] = nights[i] == 2            # there are just 2 workers on night shifts

solver = z3.Solver()
solver.add(var_vals + moornings + afternoons + nights + picky_workers)
if solver.check() == z3.sat:
    model = solver.model()
else:
    print("Your workers cannot be so picky.")
    exit(0)

# print it nicely
schedule = [["moorning " if model[vars[i * 9 + j]].as_long() == 1 else
             "afternoon" if model[vars[i * 9 + j]].as_long() == 2 else
             "night    " if model[vars[i * 9 + j]].as_long() == 3 else
             "off      " for i in range(7)] for j in range(9)]

print("Schedule for\tMonday\t\tTuesday\t\tWednesday\tThursday\tFriday\t\tSaturday\tSunday")
for i in range(9):
    print("%s\t\t" % workers[i], end='')
    for j in range(7):
        print(schedule[i][j] + "\t", end='')
    print()


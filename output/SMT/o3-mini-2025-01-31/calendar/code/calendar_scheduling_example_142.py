from z3 import *

solver = Solver()

# Meeting parameters
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
# Gloria prefers not to meet before 14:30 (i.e. 870 minutes)
solver.add(start >= 870, start + duration <= 1020)

# Helper function to add busy interval constraints:
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish by bs or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for (bs, be) in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Richard's busy intervals:
# 9:00 to 10:00 -> [540, 600]
richard_busy = [(540, 600)]
add_busy_constraints(solver, richard_busy)

# Sarah's busy intervals:
# 11:00 to 11:30 -> [660, 690]
# 14:00 to 14:30 -> [840, 870]
sarah_busy = [(660, 690), (840, 870)]
add_busy_constraints(solver, sarah_busy)

# Gloria's busy intervals:
# 9:00 to 12:30   -> [540, 750]
# 13:30 to 14:00  -> [810, 840]
# 14:30 to 15:00  -> [870, 900]
# 15:30 to 16:00  -> [930, 960]
gloria_busy = [(540, 750), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, gloria_busy)

# Kathleen's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 11:00 -> [630, 660]
# 12:00 to 12:30 -> [720, 750]
# 13:30 to 15:30 -> [810, 930]
# 16:00 to 16:30 -> [960, 990]
kathleen_busy = [(540, 570), (630, 660), (720, 750), (810, 930), (960, 990)]
add_busy_constraints(solver, kathleen_busy)

# Iterate possible start times from 870 to (1020 - duration) = 990
solution_found = False
for t in range(870, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
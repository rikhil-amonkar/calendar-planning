from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before bs starts or start on/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Richard has no meetings, so no constraints.

# Debra's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
debra_busy = [(600, 630), (750, 780), (810, 840), (900, 930)]
add_busy_constraints(solver, debra_busy)

# Matthew's busy intervals:
# 9:00 to 13:00   -> [540, 780)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 17:00  -> [960, 1020)
matthew_busy = [(540, 780), (870, 930), (960, 1020)]
add_busy_constraints(solver, matthew_busy)

# Elizabeth's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 17:00 -> [930, 1020)
elizabeth_busy = [(540, 570), (660, 690), (720, 750), (840, 900), (930, 1020)]
add_busy_constraints(solver, elizabeth_busy)

# Find a valid meeting time by iterating from the earliest possible.
solution_found = False
for t in range(540, 1020 - duration + 1):
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
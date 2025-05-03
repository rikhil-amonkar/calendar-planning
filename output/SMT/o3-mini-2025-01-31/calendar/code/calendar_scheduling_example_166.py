from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), ensure the meeting [start, start+duration)
# does not overlap with the busy period.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Sara's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
sara_busy = [(600, 630), (900, 930), (960, 1020)]
add_busy_constraints(solver, sara_busy)

# Lauren is free the entire day, so no busy constraints.

# Jose's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 17:00 -> [840, 1020)
jose_busy = [(540, 630), (660, 720), (780, 810), (840, 1020)]
add_busy_constraints(solver, jose_busy)

# Henry's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 14:00 -> [660, 840)
# 14:30 to 16:00 -> [870, 960)
henry_busy = [(600, 630), (660, 840), (870, 960)]
add_busy_constraints(solver, henry_busy)

# We look for the earliest valid meeting start time.
solution_found = False

for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
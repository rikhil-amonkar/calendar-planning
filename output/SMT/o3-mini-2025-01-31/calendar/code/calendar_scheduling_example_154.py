from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
# For each busy interval [bs, be), ensure that the meeting [start, start+duration)
# does not overlap with it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Ann is free all day, so no constraints.

# Kelly's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
kelly_busy = [(750, 780), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, kelly_busy)

# Benjamin's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 14:00 -> [750, 840)
# 15:00 to 16:30 -> [900, 990)
benjamin_busy = [(540, 630), (660, 690), (750, 840), (900, 990)]
add_busy_constraints(solver, benjamin_busy)

# Pamela's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 17:00  -> [900, 1020)
pamela_busy = [(570, 660), (690, 750), (780, 870), (900, 1020)]
add_busy_constraints(solver, pamela_busy)

# Try to find a valid meeting time by iterating over possible start times.
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
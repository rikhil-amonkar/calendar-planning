from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# The group would like to meet at their earliest availability.
# Our search will start at 9:00 (540) and return the first valid meeting time.

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish on/before bs or start on/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Angela's busy intervals:
# 10:00 to 11:30 -> [600,690)
# 12:00 to 12:30 -> [720,750)
# 13:30 to 14:00 -> [810,840)
# 15:00 to 15:30 -> [900,930)
angela_busy = [(600, 690), (720, 750), (810, 840), (900, 930)]
add_busy_constraints(solver, angela_busy)

# David's calendar is wide open (no constraints).

# Judith's busy intervals:
# 9:00 to 9:30   -> [540,570)
# 10:00 to 13:30 -> [600,810)
# 14:30 to 16:00 -> [870,960)
# 16:30 to 17:00 -> [990,1020)
judith_busy = [(540, 570), (600, 810), (870, 960), (990, 1020)]
add_busy_constraints(solver, judith_busy)

# Thomas's busy intervals:
# 9:00 to 10:00   -> [540,600)
# 11:30 to 12:30 -> [690,750)
# 13:00 to 14:00 -> [780,840)
# 14:30 to 16:00 -> [870,960)
# 16:30 to 17:00 -> [990,1020)
thomas_busy = [(540, 600), (690, 750), (780, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, thomas_busy)

# Search for the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes back to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
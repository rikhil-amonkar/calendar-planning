from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Angela's preference: she would like to avoid more meetings on Monday before 15:00.
# Enforce that the meeting must start no earlier than 15:00 (900 minutes).
solver.add(start >= 900)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting must either finish by bs or start after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Katherine's busy intervals:
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:30 -> [780, 870)
katherine_busy = [(720, 750), (780, 870)]
add_busy_constraints(solver, katherine_busy)

# Rebecca is free all day, so no constraints are added.

# Julie's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 15:30 -> [900, 930)
julie_busy = [(540, 570), (630, 660), (810, 840), (900, 930)]
add_busy_constraints(solver, julie_busy)

# Angela's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 14:00  -> [690, 840)
#   14:30 to 15:00  -> [870, 900)
#   16:30 to 17:00  -> [990, 1020)
angela_busy = [(540, 600), (630, 660), (690, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, angela_busy)

# Nicholas's busy intervals:
#   9:30 to 11:00   -> [570, 660)
#   11:30 to 13:30  -> [690, 810)
#   14:00 to 16:00  -> [840, 960)
#   16:30 to 17:00  -> [990, 1020)
nicholas_busy = [(570, 660), (690, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, nicholas_busy)

# Carl's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 12:30  -> [690, 750)
#   13:00 to 14:30  -> [780, 870)
#   15:00 to 16:00  -> [900, 960)
#   16:30 to 17:00  -> [990, 1020)
carl_busy = [(540, 660), (690, 750), (780, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, carl_busy)

# Search for the earliest valid meeting slot that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting time to within work hours:
solver.add(start >= 540, start + duration <= 1020)

# Helper function that adds a constraint for each busy interval.
# For a busy interval [bs, be), the meeting must either finish before bs or start after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Wayne's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
#   15:00 to 15:30 -> [900, 930)
wayne_busy = [(570, 600), (690, 720), (750, 780), (900, 930)]
add_busy_constraints(solver, wayne_busy)

# Larry is free the entire day, so no constraints.

# Richard's busy intervals:
#   9:30 to 10:30 -> [570, 630)
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 13:30 -> [780, 810)
richard_busy = [(570, 630), (690, 720), (780, 810)]
add_busy_constraints(solver, richard_busy)

# Sophia's busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   11:00 to 15:30 -> [660, 930)
sophia_busy = [(540, 570), (660, 930)]
add_busy_constraints(solver, sophia_busy)

# Jennifer's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 13:00 -> [630, 780)
#   13:30 to 14:30 -> [810, 870)
#   15:00 to 16:00 -> [900, 960)
jennifer_busy = [(540, 570), (630, 780), (810, 870), (900, 960)]
add_busy_constraints(solver, jennifer_busy)

# Theresa's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   11:00 to 12:00  -> [660, 720)
#   12:30 to 13:30  -> [750, 810)
#   14:30 to 15:30  -> [870, 930)
#   16:00 to 16:30  -> [960, 990)
theresa_busy = [(570, 600), (660, 720), (750, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, theresa_busy)

# We now search for the earliest meeting slot that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):  # iterate over possible start times
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
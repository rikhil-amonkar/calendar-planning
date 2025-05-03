from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Henry's preference: would rather not meet on Monday after 10:00.
# We interpret this as the meeting must finish by 10:00 (i.e., start + duration <= 600).
solver.add(start + duration <= 600)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Eric's busy intervals (in minutes):
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 15:00 -> [840, 900)
eric_busy = [
    (720, 780),
    (840, 900)
]
add_busy_constraints(solver, eric_busy)

# Henry's busy intervals (in minutes):
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 17:00 -> [960, 1020)
henry_busy = [
    (570, 600),
    (630, 660),
    (690, 750),
    (780, 810),
    (870, 900),
    (960, 1020)
]
add_busy_constraints(solver, henry_busy)

# Search for the earliest valid meeting time.
found = False
# Given Henry's constraint (meeting must finish by 600), the latest possible start is 600 - duration = 570.
for t in range(540, 571):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
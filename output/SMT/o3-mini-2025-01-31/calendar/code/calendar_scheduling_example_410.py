from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Paul's preference: he would like to avoid more meetings on Monday after 11:00.
# So the meeting must finish by 11:00 (660 minutes).
solver.add(start + duration <= 660)

# Helper function: add constraints to ensure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must finish before a busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Nathan is free the entire day, so no constraints.

# David's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 16:00 to 16:30 -> [960, 990)
david_busy = [(540, 570), (960, 990)]
add_busy_constraints(solver, david_busy)

# Robert's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 13:00 to 13:30 -> [780, 810)
robert_busy = [(570, 600), (780, 810)]
add_busy_constraints(solver, robert_busy)

# Evelyn is free the entire day, so no constraints.

# Christine's busy intervals:
# 9:00 to 10:00  -> [540, 600)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 16:00 -> [840, 960)
# 16:30 to 17:00 -> [990, 1020)
christine_busy = [(540, 600), (780, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, christine_busy)

# Kelly's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:00  -> [930, 960)
kelly_busy = [(540, 600), (630, 660), (720, 750), (810, 900), (930, 960)]
add_busy_constraints(solver, kelly_busy)

# Paul's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
paul_busy = [(540, 570), (630, 660), (690, 720), (780, 810), (840, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, paul_busy)

# Since Paul's meeting must finish by 11:00,
# the meeting could only start as early as 9:00 (540) and at latest at 10:30 (630)
found = False
for t in range(540, 630 + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
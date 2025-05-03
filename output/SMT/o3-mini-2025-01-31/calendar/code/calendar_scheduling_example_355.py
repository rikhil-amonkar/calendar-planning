from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Austin's preference: would rather not meet after 15:30,
# so enforce that the meeting finishes by 15:30 (15:30 = 930 minutes).
solver.add(start + duration <= 930)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting must either finish before bs or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Bruce is free the whole day, no constraints are added.

# Vincent's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 15:00 -> [840, 900)
#   16:30 to 17:00 -> [990, 1020)
vincent_busy = [(750, 780), (840, 900), (990, 1020)]
add_busy_constraints(solver, vincent_busy)

# Austin is free the whole day, but we already added the meeting time preference.

# Diane's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   12:00 to 13:30 -> [720, 810)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
diane_busy = [(540, 570), (600, 630), (720, 810), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, diane_busy)

# Juan's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 14:30 -> [750, 870)
#   16:00 to 17:00 -> [960, 1020)
juan_busy = [(540, 570), (690, 720), (750, 870), (960, 1020)]
add_busy_constraints(solver, juan_busy)

# Joseph's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   12:00 to 15:00  -> [720, 900)
joseph_busy = [(540, 660), (720, 900)]
add_busy_constraints(solver, joseph_busy)

# Search for the earliest valid meeting start time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
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
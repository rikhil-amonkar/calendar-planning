from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must start and end within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting must either end before bs or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Aaron is free the whole day, so no constraints are added.

# Betty's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
betty_busy = [(600, 630), (690, 720), (750, 780), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, betty_busy)

# Linda is free the whole day, so no constraints.

# Joan's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:30 -> [780, 870)
#   16:00 to 16:30 -> [960, 990)
joan_busy = [(540, 570), (600, 660), (720, 750), (780, 870), (960, 990)]
add_busy_constraints(solver, joan_busy)

# Walter's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:30 -> [810, 870)
#   15:00 to 17:00 -> [900, 1020)
walter_busy = [(540, 570), (630, 660), (690, 720), (750, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, walter_busy)

# Martha's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:30 -> [750, 810)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 16:30 -> [960, 990)
martha_busy = [(540, 570), (630, 660), (690, 720), (750, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, martha_busy)

# Since the group would like to meet at their earliest availability,
# we search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state before breaking.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
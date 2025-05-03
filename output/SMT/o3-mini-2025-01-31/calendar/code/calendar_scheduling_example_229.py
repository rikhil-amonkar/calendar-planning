from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Betty prefers to avoid meetings after 11:30,
# so we add a constraint that the meeting must finish by 11:30 (i.e., before 690).
solver.add(start + duration <= 690)

# Helper function: for each busy interval (busy_start, busy_end),
# add constraints ensuring the meeting interval [start, start+duration) does not overlap.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Either the meeting ends before a busy interval starts or starts after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Brittany is free the entire day (no busy intervals).

# Wayne has no meetings the whole day (no busy intervals).

# Betty's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 15:00 to 15:30 -> [900, 930)
betty_busy = [(630, 660), (900, 930)]
add_busy_constraints(solver, betty_busy)

# Diane's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 16:30 -> [810, 990)
diane_busy = [(540, 570), (600, 660), (690, 780), (810, 990)]
add_busy_constraints(solver, diane_busy)

# Larry's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 17:00  -> [810, 1020)
larry_busy = [(540, 660), (690, 780), (810, 1020)]
add_busy_constraints(solver, larry_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The latest valid start is 1020 - duration = 990, but due to Betty's preference,
# meeting must end by 690, so realistically, start must be <=660.
for t in range(540, 661):  # search from 9:00 (540) to 11:00 (660)
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
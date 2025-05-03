from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Willie is free the entire day, so no busy intervals.

# Marilyn's busy intervals:
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
marilyn_busy = [(840, 870), (900, 930)]
add_busy_constraints(solver, marilyn_busy)

# Charlotte's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 11:30 -> [660, 690)
#   16:00 to 16:30 -> [960, 990)
charlotte_busy = [(540, 570), (600, 630), (660, 690), (960, 990)]
add_busy_constraints(solver, charlotte_busy)

# Zachary's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:30 -> [750, 810)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 17:00 -> [960, 1020)
zachary_busy = [(540, 570), (600, 660), (690, 720), (750, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, zachary_busy)

# Noah's busy intervals:
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 14:00 -> [720, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 17:00 -> [930, 1020)
noah_busy = [(630, 690), (720, 840), (870, 900), (930, 1020)]
add_busy_constraints(solver, noah_busy)

# We want to schedule the meeting at the earliest availability.
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
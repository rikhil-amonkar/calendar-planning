from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes past midnight)

# The meeting must fit within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints so that the meeting doesn't overlap a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap the busy interval if it ends before bs or starts at or after be.
        s.add(Or(start + duration <= bs, start >= be))

# Eric's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
eric_busy = [(600, 630), (750, 780)]
add_busy_constraints(solver, eric_busy)

# Jeremy's busy intervals:
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 15:00 to 15:30 -> [900, 930)
jeremy_busy = [(660, 720), (750, 780), (900, 930)]
add_busy_constraints(solver, jeremy_busy)

# Joe is free the entire day, no busy intervals.

# Brian's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 13:00  -> [660, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 16:00  -> [870, 960)
# 16:30 to 17:00  -> [990, 1020)
brian_busy = [(540, 630), (660, 780), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, brian_busy)

# Brittany's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 12:00  -> [630, 720)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
brittany_busy = [(540, 570), (630, 720), (810, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, brittany_busy)

# Julia's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 15:00  -> [810, 900)
# 16:00 to 17:00  -> [960, 1020)
julia_busy = [(540, 660), (750, 780), (810, 900), (960, 1020)]
add_busy_constraints(solver, julia_busy)

# Find the earliest valid meeting time.
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
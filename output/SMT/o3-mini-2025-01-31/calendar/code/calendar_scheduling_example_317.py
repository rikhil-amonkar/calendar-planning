from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes from midnight)

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that ensure the meeting does not overlap a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting does not overlap the interval if it ends before the busy interval starts,
        # or starts after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Virginia is free the entire day: no constraints.

# Kevin's busy intervals:
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:00 -> [930, 960)
kevin_busy = [(870, 900), (930, 960)]
add_busy_constraints(solver, kevin_busy)

# Kimberly's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 15:30 -> [900, 930)
kimberly_busy = [(570, 630), (690, 720), (750, 780), (810, 840), (900, 930)]
add_busy_constraints(solver, kimberly_busy)

# Lawrence's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:00 -> [780, 840)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 16:30 -> [960, 990)
lawrence_busy = [(600, 630), (660, 690), (720, 750), (780, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, lawrence_busy)

# Donna's busy intervals:
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 15:00 -> [720, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
donna_busy = [(600, 660), (720, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, donna_busy)

# Joe's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 16:00 -> [870, 960)
#   16:30 to 17:00 -> [990, 1020)
joe_busy = [(570, 600), (690, 750), (780, 810), (870, 960), (990, 1020)]
add_busy_constraints(solver, joe_busy)

# Search for the earliest valid meeting start time by iterating over possible start times (in minutes).
found = False
for t in range(540, 1020 - duration + 1):  # from 9:00 (540) to latest start time (990)
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
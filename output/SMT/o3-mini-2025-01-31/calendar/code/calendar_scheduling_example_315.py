from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(s, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting does not overlap a busy interval if it ends before the busy period starts,
        # or starts after the busy period ends.
        s.add(Or(start + duration <= busy_start, start >= busy_end))

# Gloria is free the whole day, so no constraints.

# Roy's busy intervals:
#   9:00 to 10:00 -> [540, 600)
roy_busy = [(540, 600)]
add_busy_constraints(solver, roy_busy)

# Kimberly's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 12:00 -> [660, 720)
#   16:30 to 17:00 -> [990, 1020)
kimberly_busy = [(540, 570), (660, 720), (990, 1020)]
add_busy_constraints(solver, kimberly_busy)

# Robert's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   13:00 to 13:30 -> [780, 810)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
robert_busy = [(540, 570), (600, 660), (780, 810), (840, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, robert_busy)

# Jesse's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 14:00 -> [780, 840)
#   14:30 to 15:00 -> [870, 900)
jesse_busy = [(540, 570), (600, 660), (690, 750), (780, 840), (870, 900)]
add_busy_constraints(solver, jesse_busy)

# Sophia's busy intervals:
#   9:00 to 12:00  -> [540, 720)
#   13:00 to 17:00 -> [780, 1020)
sophia_busy = [(540, 720), (780, 1020)]
add_busy_constraints(solver, sophia_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # t from 540 to 990 inclusive.
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
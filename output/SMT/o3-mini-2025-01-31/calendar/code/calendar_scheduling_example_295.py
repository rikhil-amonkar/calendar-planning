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

# Helper function to enforce that meeting does not overlap with any busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting and busy interval do not overlap if:
        # meeting is entirely before busy interval or after busy interval.
        s.add(Or(start + duration <= bs, start >= be))

# Joan is free the entire day, so no constraints.

# Gloria's busy intervals:
#   9:00 to 10:00 -> [540, 600)
#   11:30 to 12:00 -> [690, 720)
#   16:30 to 17:00 -> [990, 1020)
gloria_busy = [(540, 600), (690, 720), (990, 1020)]
add_busy_constraints(solver, gloria_busy)

# Ann's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   10:30 to 11:00 -> [630, 660)
#   12:00 to 13:00 -> [720, 780)
#   16:00 to 17:00 -> [960, 1020)
ann_busy = [(570, 600), (630, 660), (720, 780), (960, 1020)]
add_busy_constraints(solver, ann_busy)

# Dorothy's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:30  -> [630, 690)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 15:30  -> [840, 930)
#   16:00 to 17:00  -> [960, 1020)
dorothy_busy = [(540, 600), (630, 690), (780, 810), (840, 930), (960, 1020)]
add_busy_constraints(solver, dorothy_busy)

# David's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 15:30  -> [600, 930)
#   16:00 to 17:00  -> [960, 1020)
david_busy = [(540, 570), (600, 930), (960, 1020)]
add_busy_constraints(solver, david_busy)

# We now search for the earliest meeting start that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Push current solver state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
              start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
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

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting doesn't overlap the busy interval if it ends on or before the interval starts,
        # or it starts on or after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Grace's busy intervals:
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 12:30 -> [720, 750)
#   15:00 to 15:30 -> [900, 930)
grace_busy = [(630, 690), (720, 750), (900, 930)]
add_busy_constraints(solver, grace_busy)

# Ralph's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   16:00 to 16:30 -> [960, 990)
ralph_busy = [(660, 690), (960, 990)]
add_busy_constraints(solver, ralph_busy)

# Harold is free the entire day - no constraints needed.

# Kayla's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:30 to 17:00 -> [810, 1020)
kayla_busy = [(600, 630), (660, 690), (720, 750), (810, 1020)]
add_busy_constraints(solver, kayla_busy)

# Andrea's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 13:00 -> [660, 780)
#   13:30 to 17:00 -> [810, 1020)
andrea_busy = [(540, 630), (660, 780), (810, 1020)]
add_busy_constraints(solver, andrea_busy)

# Maria's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 13:00 -> [660, 780)
#   15:00 to 16:30 -> [900, 990)
maria_busy = [(540, 630), (660, 780), (900, 990)]
add_busy_constraints(solver, maria_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # from 9:00 (540) to latest start 16:30 (990)
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
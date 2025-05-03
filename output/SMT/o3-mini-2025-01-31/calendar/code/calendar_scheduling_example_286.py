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

# Helper function: add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting should either finish on or before the busy interval starts,
        # or begin on or after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Ralph's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   15:00 to 15:30 -> [900, 930)
ralph_busy = [(540, 630), (900, 930)]
add_busy_constraints(solver, ralph_busy)

# John's calendar is free, so no constraints.

# Sharon's calendar is free, so no constraints.

# Sophia's busy intervals:
#   9:30 to 13:30  -> [570, 810)
#   14:00 to 17:00 -> [840, 1020)
sophia_busy = [(570, 810), (840, 1020)]
add_busy_constraints(solver, sophia_busy)

# Samantha's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   12:00 to 13:30  -> [720, 810)
#   15:00 to 15:30  -> [900, 930)
#   16:30 to 17:00  -> [990, 1020)
samantha_busy = [(540, 630), (720, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, samantha_busy)

# Search for a valid meeting start time.
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
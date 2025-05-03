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

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap the busy interval if it ends before the interval starts
        # or starts after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Natalie’s busy intervals:
#   14:30 to 15:00 -> [870, 900)
#   16:00 to 16:30 -> [960, 990)
natalie_busy = [(870, 900), (960, 990)]
add_busy_constraints(solver, natalie_busy)

# Evelyn is free the entire day; no constraints needed.

# Andrea is free the entire day; no constraints needed.

# Kimberly’s busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 13:30  -> [750, 810)
#   14:30 to 15:30  -> [870, 930)
kimberly_busy = [(540, 600), (630, 690), (750, 810), (870, 930)]
add_busy_constraints(solver, kimberly_busy)

# Dennis’ busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 14:00  -> [720, 840)
#   14:30 to 16:00  -> [870, 960)
dennis_busy = [(540, 600), (660, 690), (720, 840), (870, 960)]
add_busy_constraints(solver, dennis_busy)

# Larry’s busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   12:00 to 17:00  -> [720, 1020)
larry_busy = [(540, 660), (720, 1020)]
add_busy_constraints(solver, larry_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # Candidate start times from 9:00 (540) to 16:30 (990)
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
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for a list of busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting avoids overlap if it ends on or before the busy interval starts
        # or starts on or after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Ralph's busy intervals:
#   14:00 to 14:30 -> [840, 870)
#   15:30 to 16:00 -> [930, 960)
ralph_busy = [(840, 870), (930, 960)]
add_busy_constraints(solver, ralph_busy)

# Kenneth is free the entire day, so no constraints are necessary.

# Diane's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   13:00 to 13:30  -> [780, 810)
#   15:00 to 15:30  -> [900, 930)
#   16:30 to 17:00  -> [990, 1020)
diane_busy = [(540, 630), (780, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, diane_busy)

# Kayla's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   12:00 to 15:00  -> [720, 900)
#   15:30 to 16:00  -> [930, 960)
#   16:30 to 17:00  -> [990, 1020)
kayla_busy = [(600, 660), (720, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, kayla_busy)

# Bruce's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 14:30  -> [750, 870)
#   16:30 to 17:00  -> [990, 1020)
bruce_busy = [(570, 600), (630, 690), (750, 870), (990, 1020)]
add_busy_constraints(solver, bruce_busy)

# Jesse's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:30  -> [750, 810)
#   14:30 to 15:00  -> [870, 900)
#   15:30 to 16:00  -> [930, 960)
#   16:30 to 17:00  -> [990, 1020)
jesse_busy = [(600, 660), (690, 720), (750, 810), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, jesse_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # from 9:00 (540) to 16:30 (990)
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
from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional preference:
# Alexis would rather not meet before 16:30 (which is 990 minutes).
solver.add(start >= 990)

# Helper function: Add constraints to ensure the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap the busy interval if it ends on or before the interval starts
        # or starts on or after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Logan's busy intervals:
#   10:00 to 10:30  -> [600, 630)
#   14:00 to 14:30  -> [840, 870)
logan_busy = [(600, 630), (840, 870)]
add_busy_constraints(solver, logan_busy)

# Kathryn is free all day, so no constraints.

# Jennifer's calendar is wide open, so no constraints.

# Alexis's busy intervals:
#   Blocked from 9:00 to 11:00 -> [540, 660)
#   Blocked from 12:00 to 14:00 -> [720, 840)
#   Blocked from 15:00 to 16:00 -> [900, 960)
alexis_busy = [(540, 660), (720, 840), (900, 960)]
add_busy_constraints(solver, alexis_busy)

# Roy's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 15:00  -> [840, 900)
#   16:00 to 16:30  -> [960, 990)
roy_busy = [(540, 630), (720, 750), (780, 810), (840, 900), (960, 990)]
add_busy_constraints(solver, roy_busy)

# Search for a valid meeting start time.
# Since Alexis prefers times starting at or after 16:30,
# our search begins at 16:30 (990 minutes).
found = False
for t in range(990, 1020 - duration + 1):
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
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

# Helper function: Add constraints to ensure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap the busy interval if it finishes before the interval starts,
        # or it starts after the interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Frances has no meetings, so no busy intervals.
# Jack's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   14:00 to 14:30 -> [840, 870)
#   16:00 to 17:00 -> [960, 1020)
jack_busy = [(630, 660), (840, 870), (960, 1020)]
add_busy_constraints(solver, jack_busy)

# Susan's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 14:30 -> [840, 870)
susan_busy = [(750, 780), (840, 870)]
add_busy_constraints(solver, susan_busy)

# Scott's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:00 to 12:30  -> [720, 750)
#   15:00 to 16:00  -> [900, 960)
#   16:30 to 17:00  -> [990, 1020)
scott_busy = [(540, 600), (630, 690), (720, 750), (900, 960), (990, 1020)]
add_busy_constraints(solver, scott_busy)

# Joan's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 14:00  -> [660, 840)
#   14:30 to 16:00  -> [870, 960)
#   16:30 to 17:00  -> [990, 1020)
joan_busy = [(540, 600), (660, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, joan_busy)

# Search for a valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # iterate possible start times
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
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

# Lauren's preference: avoid more meetings after 13:00 (780 minutes).
# Thus, the meeting should be entirely before 13:00.
solver.add(start + duration <= 780)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting and the busy interval don't overlap if either:
        # the meeting ends on or before the busy interval starts, or 
        # the meeting begins on or after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Ryan is free all day (no busy intervals).

# Susan is free all day (no busy intervals).

# Joyce's busy intervals:
#   10:00 to 10:30  -> [600, 630)
#   15:30 to 16:00  -> [930, 960)
joyce_busy = [(600, 630), (930, 960)]
add_busy_constraints(solver, joyce_busy)

# Jacob's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   12:30 to 13:00  -> [750, 780)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
jacob_busy = [(540, 660), (750, 780), (900, 930), (960, 1020)]
add_busy_constraints(solver, jacob_busy)

# Lauren's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 17:00  -> [870, 1020)
lauren_busy = [(540, 600), (780, 810), (870, 1020)]
add_busy_constraints(solver, lauren_busy)

# Because of Lauren's preference, our meeting must entirely finish before 13:00.
# We have already enforced: start + duration <= 780.
# So, we only need to consider meeting start times that satisfy that.
# Let's search for a valid meeting start time.
found = False
# Iterate possible start times from earliest (540) up to the latest possible that satisfies start+duration <=780.
for t in range(540, 780 - duration + 1):
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
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap a busy interval if it ends on or before the busy period starts,
        # or starts on or after the busy period ends.
        s.add(Or(start + duration <= bs, start >= be))

# Diane's busy intervals:
#   9:00 to 9:30  -> [540, 570)
#   12:30 to 13:00-> [750, 780)
diane_busy = [(540, 570), (750, 780)]
add_busy_constraints(solver, diane_busy)

# Christian's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
christian_busy = [(690, 720), (750, 780)]
add_busy_constraints(solver, christian_busy)

# Jeffrey is free the entire day; no constraints.

# Vincent's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:30 to 13:30 -> [690, 810)
#   14:30 to 15:00 -> [870, 900)
#   16:30 to 17:00 -> [990, 1020)
vincent_busy = [(570, 630), (690, 810), (870, 900), (990, 1020)]
add_busy_constraints(solver, vincent_busy)

# Ethan's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   13:30 to 14:30  -> [810, 870)
#   15:00 to 17:00  -> [900, 1020)
ethan_busy = [(540, 660), (690, 720), (750, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, ethan_busy)

# Christine's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 16:30  -> [690, 990)
christine_busy = [(540, 660), (690, 990)]
add_busy_constraints(solver, christine_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # Candidate start times from 9:00 to 16:30
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
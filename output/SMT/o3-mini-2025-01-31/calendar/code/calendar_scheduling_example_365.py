from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Sarah's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   15:00 to 15:30 -> [900, 930)
sarah_busy = [(690, 720), (900, 930)]
add_busy_constraints(solver, sarah_busy)

# Russell is free all day (no constraints)

# Michael's busy intervals:
#   10:30 to 11:30 -> [630, 690)
michael_busy = [(630, 690)]
add_busy_constraints(solver, michael_busy)

# Charles's busy intervals:
#   10:00 to 12:00 -> [600, 720)
#   13:00 to 14:00 -> [780, 840)
#   14:30 to 15:00 -> [870, 900)
#   16:30 to 17:00 -> [990, 1020)
charles_busy = [(600, 720), (780, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, charles_busy)

# Heather's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 13:30 -> [660, 810)
#   14:30 to 15:00 -> [870, 900)
#   16:00 to 16:30 -> [960, 990)
heather_busy = [(540, 630), (660, 810), (870, 900), (960, 990)]
add_busy_constraints(solver, heather_busy)

# Sharon's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 12:00 -> [600, 720)
#   12:30 to 13:30 -> [750, 810)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
sharon_busy = [(540, 570), (600, 720), (750, 810), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, sharon_busy)

# Now, iterate over possible start times within the allowed hours to find a valid meeting time.
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
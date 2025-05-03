from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Emily cannot meet before 9:30, so we use 9:30 (570 minutes) as the effective start.
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must start no earlier than 9:30 and end by 17:00.
solver.add(start >= 570, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Kenneth's schedule: free all day, no constraints needed.

# Melissa's schedule: free all day, no constraints needed.

# Joan's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   12:30 to 13:30  -> [750, 810)
#   15:00 to 15:30  -> [900, 930)
#   16:30 to 17:00  -> [990, 1020)
joan_busy = [(600, 660), (750, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, joan_busy)

# Emily's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   12:30 to 14:00  -> [750, 840)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
emily_busy = [(600, 660), (750, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, emily_busy)
# Also, Emily cannot meet before 9:30, which is already enforced by setting start >= 570.

# Brandon's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 14:00 -> [750, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 17:00 -> [930, 1020)
brandon_busy = [(570, 630), (660, 690), (750, 840), (870, 900), (930, 1020)]
add_busy_constraints(solver, brandon_busy)

# Christopher's busy intervals:
#   11:30 to 14:00 -> [690, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
christopher_busy = [(690, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, christopher_busy)

# Iterate over possible meeting start times within the allowed time range to find a valid meeting time.
found = False
for t in range(570, 1020 - duration + 1):
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
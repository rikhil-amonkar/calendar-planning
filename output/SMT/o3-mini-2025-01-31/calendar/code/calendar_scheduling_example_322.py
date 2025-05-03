from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain meeting start time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting
# does not overlap with given busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting avoids overlapping if it ends at or before busy interval starts
        # or starts at or after busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Kathryn's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   12:30 to 14:00 -> [750, 840)
kathryn_busy = [(570, 600), (750, 840)]
add_busy_constraints(solver, kathryn_busy)

# Jessica has no meetings; so no busy intervals.

# Ruth's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   14:30 to 15:00 -> [870, 900)
ruth_busy = [(750, 780), (870, 900)]
add_busy_constraints(solver, ruth_busy)

# Matthew's busy intervals:
#   9:00 to 10:00 -> [540, 600)
#   11:30 to 13:00 -> [690, 780)
#   13:30 to 15:00 -> [810, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
matthew_busy = [(540, 600), (690, 780), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, matthew_busy)

# Jennifer's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
#   15:00 to 17:00 -> [900, 1020)
jennifer_busy = [(540, 570), (600, 630), (690, 720), (750, 780), (900, 1020)]
add_busy_constraints(solver, jennifer_busy)

# Alice's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   12:00 to 12:30 -> [720, 750)
#   15:00 to 17:00 -> [900, 1020)
alice_busy = [(540, 630), (720, 750), (900, 1020)]
add_busy_constraints(solver, alice_busy)

# Iterate over possible start times to find the earliest valid meeting time.
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
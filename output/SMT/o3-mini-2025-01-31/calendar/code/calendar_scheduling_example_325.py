from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)
# Additionally, Jose does not want to meet after 15:30.
# This means the meeting must finish by 15:30, i.e. start + duration <= 930.
solver.add(start + duration <= 930)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting avoids overlapping a busy interval if it
        # finishes by the start of the interval or starts after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Jose's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 13:00 -> [750, 780)
jose_busy = [(660, 690), (750, 780)]
add_busy_constraints(solver, jose_busy)

# Keith's busy intervals:
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
keith_busy = [(840, 870), (900, 930)]
add_busy_constraints(solver, keith_busy)

# Logan's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   12:00 to 12:30  -> [720, 750)
#   15:00 to 15:30  -> [900, 930)
logan_busy = [(540, 600), (720, 750), (900, 930)]
add_busy_constraints(solver, logan_busy)

# Megan's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:00 to 12:00  -> [660, 720)
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 16:30  -> [870, 990)
megan_busy = [(540, 630), (660, 720), (780, 810), (870, 990)]
add_busy_constraints(solver, megan_busy)

# Gary's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 10:30  -> [600, 630)
#   11:30 to 13:00  -> [690, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 16:30  -> [870, 990)
gary_busy = [(540, 570), (600, 630), (690, 780), (810, 840), (870, 990)]
add_busy_constraints(solver, gary_busy)

# Bobby's busy intervals:
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 16:00  -> [780, 960)
bobby_busy = [(660, 690), (720, 750), (780, 960)]
add_busy_constraints(solver, bobby_busy)

# Search for the earliest valid meeting start time.
found = False
# Meeting must finish by 15:30 → start + 30 <= 930, hence start <= 900.
for t in range(540, 901):  # iterate possible start times from 9:00 (540) to 15:00 (900)
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
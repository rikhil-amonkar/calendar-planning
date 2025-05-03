from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# Constrain the meeting to fit within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that ensure the meeting
# does not overlap any busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting does not overlap a busy interval if either:
        #   (a) it ends before the busy interval starts, or
        #   (b) it starts at or after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Nicholas and Emma are free the entire day, so no constraints for them.

# Catherine's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   11:30 to 12:00  -> [690, 720)
#   13:30 to 14:00  -> [810, 840)
#   15:30 to 16:00  -> [930, 960)
catherine_busy = [(540, 570), (690, 720), (810, 840), (930, 960)]
add_busy_constraints(solver, catherine_busy)

# Steven's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 16:30 -> [600, 990)
steven_busy = [(540, 570), (600, 990)]
add_busy_constraints(solver, steven_busy)

# Adam's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 13:00  -> [630, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 16:30  -> [870, 990)
adam_busy = [(540, 600), (630, 780), (810, 840), (870, 990)]
add_busy_constraints(solver, adam_busy)

# Lori's busy intervals:
#   9:00 to 11:30   -> [540, 690)
#   12:30 to 13:30  -> [750, 810)
#   16:00 to 16:30  -> [960, 990)
lori_busy = [(540, 690), (750, 810), (960, 990)]
add_busy_constraints(solver, lori_busy)

# We now search for an earliest valid meeting time.
# Note: Due to Steven's long block from 10:00 to 16:30, the only possibility
# is before 10:00 or after 16:30. Since Adam is busy until 10:00,
# the meeting must be scheduled after 16:30.
found = False
for t in range(540, 1020 - duration + 1):  # t from 540 to 990 inclusive
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
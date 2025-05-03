from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(s, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting does not overlap a busy interval if it ends on or before the busy period starts,
        # or starts on or after the busy period ends.
        s.add(Or(start + duration <= busy_start, start >= busy_end))

# Lori and Kelly have no meetings, so no constraints needed for them.

# Tyler's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:00 -> [690, 720)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
tyler_busy = [(600, 630), (690, 720), (930, 960), (990, 1020)]
add_busy_constraints(solver, tyler_busy)

# Julie's busy intervals:
#   9:00 to 12:00   -> [540, 720)
#   12:30 to 13:00  -> [750, 780)
#   13:30 to 14:30  -> [810, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
julie_busy = [(540, 720), (750, 780), (810, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, julie_busy)

# Andrea's busy intervals:
#   9:00 to 13:00   -> [540, 780)
#   13:30 to 15:30  -> [810, 930)
#   16:00 to 17:00  -> [960, 1020)
andrea_busy = [(540, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, andrea_busy)

# Gabriel's busy intervals:
#   9:00 to 12:30   -> [540, 750)
#   13:30 to 17:00  -> [810, 1020)
gabriel_busy = [(540, 750), (810, 1020)]
add_busy_constraints(solver, gabriel_busy)

# Search for the earliest valid meeting start time.
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
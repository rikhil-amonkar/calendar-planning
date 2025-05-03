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

# Helper function: add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting must finish before a busy interval starts, or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Aaron's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:30 -> [690, 750)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 16:30 -> [960, 990)
aaron_busy = [(600, 630), (690, 750), (870, 930), (960, 990)]
add_busy_constraints(solver, aaron_busy)

# Lori has no meetings the whole day, so no constraints needed.

# Jordan is free all day, so no constraints needed.

# Noah's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 13:00 -> [600, 780)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 16:00 -> [900, 960)
noah_busy = [(540, 570), (600, 780), (840, 870), (900, 960)]
add_busy_constraints(solver, noah_busy)

# Susan's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 16:00  -> [600, 960)
#   16:30 to 17:00  -> [990, 1020)
susan_busy = [(540, 570), (600, 960), (990, 1020)]
add_busy_constraints(solver, susan_busy)

# Search for a valid meeting start time.
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
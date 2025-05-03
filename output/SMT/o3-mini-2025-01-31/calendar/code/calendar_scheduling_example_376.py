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

# Helper function: for each busy interval [bs, be), enforce that the meeting does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish before a busy interval starts, or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Larry's busy intervals:
#   12:00 to 13:00 -> [720, 780)
#   14:30 to 15:30 -> [870, 930)
larry_busy = [(720, 780), (870, 930)]
add_busy_constraints(solver, larry_busy)

# Angela's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   14:30 to 15:00 -> [870, 900)
angela_busy = [(630, 660), (870, 900)]
add_busy_constraints(solver, angela_busy)

# Christina is free the entire day so no constraints.

# Scott's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:30 -> [780, 870)
#   15:00 to 16:00 -> [900, 960)
scott_busy = [(570, 630), (720, 750), (780, 870), (900, 960)]
add_busy_constraints(solver, scott_busy)

# Matthew's busy intervals:
#   9:30 to 11:30  -> [570, 690)
#   12:00 to 15:00 -> [720, 900)
#   16:00 to 17:00 -> [960, 1020)
matthew_busy = [(570, 690), (720, 900), (960, 1020)]
add_busy_constraints(solver, matthew_busy)

# Charlotte's busy intervals:
#   9:00 to 11:30   -> [540, 690)
#   12:00 to 12:30   -> [720, 750)
#   13:00 to 13:30   -> [780, 810)
#   14:30 to 15:00   -> [870, 900)
#   15:30 to 16:30   -> [930, 990)
charlotte_busy = [(540, 690), (720, 750), (780, 810), (870, 900), (930, 990)]
add_busy_constraints(solver, charlotte_busy)

# Iterate over possible start times (minute by minute) within the work period.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within the working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval, add constraint that the meeting does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting must end at or before the busy interval starts, or start at or after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Diane's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   14:30 to 15:00 -> [870, 900)
diane_busy = [(600, 630), (870, 900)]
add_busy_constraints(solver, diane_busy)

# Rachel's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 16:30 -> [960, 990)
rachel_busy = [(690, 720), (780, 810), (900, 930), (960, 990)]
add_busy_constraints(solver, rachel_busy)

# Amber's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 16:00 -> [900, 960)
#   16:30 to 17:00 -> [990, 1020)
amber_busy = [(540, 570), (750, 780), (810, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, amber_busy)

# Shirley's busy intervals:
#   10:00 to 11:00 -> [600, 660)
#   11:30 to 12:00 -> [690, 720)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 17:00 -> [900, 1020)
shirley_busy = [(600, 660), (690, 720), (810, 840), (900, 1020)]
add_busy_constraints(solver, shirley_busy)

# Joshua's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 15:00 -> [810, 900)
#   16:00 to 16:30 -> [960, 990)
joshua_busy = [(540, 630), (750, 780), (810, 900), (960, 990)]
add_busy_constraints(solver, joshua_busy)

# Lisa's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   12:30 to 14:00 -> [750, 840)
#   15:00 to 17:00 -> [900, 1020)
lisa_busy = [(570, 600), (750, 840), (900, 1020)]
add_busy_constraints(solver, lisa_busy)

# Since we want the earliest availability, iterate minute-by-minute starting from 540
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("The earliest valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
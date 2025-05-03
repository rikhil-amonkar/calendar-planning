from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting is non-overlapping with a busy interval if it ends 
        # before the busy period starts, or starts after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Dennis's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   14:30 to 15:00 -> [870, 900)
dennis_busy = [(570, 600), (870, 900)]
add_busy_constraints(solver, dennis_busy)

# Ralph's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 13:30 -> [780, 810)
ralph_busy = [(630, 660), (690, 750), (780, 810)]
add_busy_constraints(solver, ralph_busy)

# Jesse's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 13:00 -> [720, 780)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 16:00 -> [930, 960)
jesse_busy = [(660, 690), (720, 780), (840, 900), (930, 960)]
add_busy_constraints(solver, jesse_busy)

# Deborah's busy intervals:
#   9:00 to 10:00  -> [540, 600)
#   10:30 to 12:00 -> [630, 720)
#   13:00 to 15:00 -> [780, 900)
#   15:30 to 17:00 -> [930, 1020)
deborah_busy = [(540, 600), (630, 720), (780, 900), (930, 1020)]
add_busy_constraints(solver, deborah_busy)

# Karen's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 13:30 -> [720, 810)
#   14:00 to 17:00 -> [840, 1020)
karen_busy = [(540, 570), (630, 690), (720, 810), (840, 1020)]
add_busy_constraints(solver, karen_busy)

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
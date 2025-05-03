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

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Pamela's calendar is wide open, so no busy intervals.

# Randy's busy intervals:
#   10:30 to 12:00 -> [630, 720)
#   14:30 to 15:30 -> [870, 930)
#   16:30 to 17:00 -> [990, 1020)
randy_busy = [(630, 720), (870, 930), (990, 1020)]
add_busy_constraints(solver, randy_busy)

# Elijah's busy intervals:
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 15:30 -> [900, 930)
elijah_busy = [(780, 810), (900, 930)]
add_busy_constraints(solver, elijah_busy)

# Jerry's busy intervals:
#   9:00 to 10:00  -> [540, 600)
#   10:30 to 15:30 -> [630, 930)
#   16:00 to 17:00 -> [960, 1020)
jerry_busy = [(540, 600), (630, 930), (960, 1020)]
add_busy_constraints(solver, jerry_busy)

# Kevin's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00  -> [600, 660)
#   12:30 to 13:30  -> [750, 810)
#   14:00 to 14:30  -> [840, 870)
#   16:00 to 17:00  -> [960, 1020)
kevin_busy = [(540, 570), (600, 660), (750, 810), (840, 870), (960, 1020)]
add_busy_constraints(solver, kevin_busy)

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
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Ensure the meeting is within the work day.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: adds constraints to make sure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Rebecca is free the entire day - no busy intervals.
# Alexander is free the entire day - no busy intervals.

# Angela's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
angela_busy = [(690, 720), (750, 780), (810, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, angela_busy)

# Beverly's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 15:00 -> [630, 900)
# 15:30 to 16:30 -> [930, 990)
beverly_busy = [(570, 600), (630, 900), (930, 990)]
add_busy_constraints(solver, beverly_busy)

# Peter's busy intervals:
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
# 16:30 to 17:00 -> [990, 1020)
peter_busy = [(570, 660), (690, 720), (780, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, peter_busy)

# Search for a valid meeting start time from 9:00 to 17:00.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint: David does not want to meet before 14:00 (840 minutes).
solver.add(start >= 840)

# Helper function: For each busy interval (busy_start, busy_end),
# add constraints ensuring the meeting [start, start+duration) does not overlap the interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Natalie is free the entire day (no constraints).

# David's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
david_busy = [(690, 720), (870, 900)]
add_busy_constraints(solver, david_busy)

# Douglas's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
douglas_busy = [(570, 600), (690, 720), (780, 810), (870, 900)]
add_busy_constraints(solver, douglas_busy)

# Ralph's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
ralph_busy = [(540, 570), (600, 660), (690, 750), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, ralph_busy)

# Jordan's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 17:00  -> [930, 1020)
jordan_busy = [(540, 600), (720, 750), (780, 810), (870, 900), (930, 1020)]
add_busy_constraints(solver, jordan_busy)

# Now, search for the earliest valid meeting time.
solution_found = False
# The latest valid start is 1020 - duration = 990.
for t in range(840, 991):
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
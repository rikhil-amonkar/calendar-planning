from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval (busy_start, busy_end), add constraints ensuring
# that the meeting interval [start, start+duration) does not overlap the busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Betty's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
# 16:00 to 17:00 -> [960, 1020)
betty_busy = [(600, 630), (750, 780), (960, 1020)]
add_busy_constraints(solver, betty_busy)

# Olivia is free the whole day, so no busy intervals.

# Brandon's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
brandon_busy = [(690, 720), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, brandon_busy)

# Lori's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 15:00 -> [780, 900)
lori_busy = [(570, 600), (660, 750), (780, 900)]
add_busy_constraints(solver, lori_busy)

# Rachel's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 17:00 -> [900, 1020)
rachel_busy = [(540, 630), (660, 690), (720, 750), (780, 810), (900, 1020)]
add_busy_constraints(solver, rachel_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The latest valid start is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
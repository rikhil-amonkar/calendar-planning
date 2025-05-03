from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting [start, start+duration)
# does not overlap with any busy interval [bs, be)
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Ensure meeting ends before busy interval starts OR starts at or after busy interval ends
        solver.add(Or(start + duration <= bs, start >= be))

# Jean is free all day, so no constraints for Jean.

# Dennis's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
dennis_busy = [(630, 660), (720, 750), (870, 900), (960, 990)]
add_busy_constraints(solver, dennis_busy)

# Ruth's busy intervals:
# 9:30 to 12:00  -> [570, 720)
# 12:30 to 13:30 -> [750, 810)
# 15:00 to 16:30 -> [900, 990)
ruth_busy = [(570, 720), (750, 810), (900, 990)]
add_busy_constraints(solver, ruth_busy)

# Eugene's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
eugene_busy = [(540, 570), (660, 690), (720, 750), (780, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, eugene_busy)

# Try to find a valid meeting time by iterating over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
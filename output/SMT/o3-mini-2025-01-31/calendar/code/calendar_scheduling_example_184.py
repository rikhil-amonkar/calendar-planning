from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')

# Meeting must start and finish within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval
# [start, start+duration) does not overlap with a given busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Raymond's busy intervals:
#  9:30 to 10:00  -> [570, 600)
# 12:30 to 14:30  -> [750, 870)
# 15:30 to 16:00  -> [930, 960)
raymond_busy = [(570, 600), (750, 870), (930, 960)]
add_busy_constraints(solver, raymond_busy)

# Sophia has no meetings the whole day (no busy intervals).

# Lori's busy intervals:
#  9:00 to 9:30   -> [540, 570)
# 10:30 to 13:00  -> [630, 780)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 17:00  -> [930, 1020)
lori_busy = [(540, 570), (630, 780), (870, 900), (930, 1020)]
add_busy_constraints(solver, lori_busy)

# Dorothy's busy intervals:
#  9:00 to 13:30  -> [540, 810)
# 14:00 to 15:00  -> [840, 900)
# 16:00 to 16:30  -> [960, 990)
dorothy_busy = [(540, 810), (840, 900), (960, 990)]
add_busy_constraints(solver, dorothy_busy)

# Find the earliest valid meeting time.
solution_found = False
# Meeting start times can be from 540 to 990 inclusive.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
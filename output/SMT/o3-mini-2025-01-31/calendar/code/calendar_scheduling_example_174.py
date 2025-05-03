from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Enforce that the meeting [start, start+duration) does not overlap with the busy interval [bs, be).
        solver.add(Or(start + duration <= bs, start >= be))

# Kevin's busy intervals.
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 16:00 -> [870, 960)
kevin_busy = [(690, 720), (870, 960)]
add_busy_constraints(solver, kevin_busy)

# David's busy intervals.
# 10:00 to 11:00 -> [600, 660)
david_busy = [(600, 660)]
add_busy_constraints(solver, david_busy)

# Stephen's busy intervals.
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 13:00  -> [720, 780)
# 14:00 to 15:30  -> [840, 930)
# 16:00 to 17:00  -> [960, 1020)
stephen_busy = [(540, 690), (720, 780), (840, 930), (960, 1020)]
add_busy_constraints(solver, stephen_busy)

# Helen's busy intervals.
# 9:00 to 13:30   -> [540, 810)
# 14:30 to 17:00  -> [870, 1020)
helen_busy = [(540, 810), (870, 1020)]
add_busy_constraints(solver, helen_busy)

# Find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Lauren's preference: does not want to meet after 11:30.
# This means the meeting must finish by 11:30 (which is 690 minutes after midnight).
solver.add(start + duration <= 690)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Lauren's busy intervals: none (she is free the whole day)
lauren_busy = []
add_busy_constraints(solver, lauren_busy)

# Ruth's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:30 -> [630, 750)
# (Other intervals exist later in the day but the meeting must finish by 11:30, so they won't affect the solution)
ruth_busy = [
    (540, 570),
    (630, 750)
]
add_busy_constraints(solver, ruth_busy)

# Search for the earliest valid meeting time.
found = False
# Given the constraint start+duration <= 690, the latest start is 690 - 60 = 630.
for t in range(540, 631):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
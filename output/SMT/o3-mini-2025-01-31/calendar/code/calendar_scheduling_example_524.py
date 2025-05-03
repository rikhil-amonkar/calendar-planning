from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration of 1 hour
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint:
# Logan cannot meet before 10:30. (10:30 is 630 minutes.)
solver.add(start >= 630)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure the meeting [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Katherine's busy intervals: free the entire day, so no busy intervals.
katherine_busy = []

# Logan's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 17:00 -> [870, 1020)
logan_busy = [
    (540, 570),
    (630, 660),
    (810, 840),
    (870, 1020)
]
add_busy_constraints(solver, logan_busy)

# Since Katherine is free, we don't add any constraints for her calendar.

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - duration = 960.
# Also, we already have the constraint that start >= 630.
for t in range(630, 961):
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
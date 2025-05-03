from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration of 1 hour
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Ruth has no meetings, so no constraints for Ruth.

# Kayla's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 13:00 to 17:00 -> [780, 1020)
kayla_busy = [
    (540, 570),
    (600, 690),
    (780, 1020)
]
add_busy_constraints(solver, kayla_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - 60 = 960.
for t in range(540, 961):
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
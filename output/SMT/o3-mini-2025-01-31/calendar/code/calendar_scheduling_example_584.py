from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: the meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting [start, start+duration) does not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Emma's calendar is wide open so no constraints for her.

# Henry's busy intervals (in minutes since midnight):
# 9:00 to 13:00  -> [540, 780)
# 14:00 to 17:00 -> [840, 1020)
henry_busy = [
    (540, 780),
    (840, 1020)
]
add_busy_constraints(solver, henry_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest start time is 1020 - 30 = 990.
for t in range(540, 991):
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
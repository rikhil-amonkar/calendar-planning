from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Define a helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # the meeting [start, start+duration) must not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Robert's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:00 -> [630, 720)
robert_busy = [
    (540, 570),
    (630, 720)
]
add_busy_constraints(solver, robert_busy)

# Bruce's busy intervals (in minutes):
# 9:00 to 10:00  -> [540, 600)
# 11:00 to 17:00 -> [660, 1020)
bruce_busy = [
    (540, 600),
    (660, 1020)
]
add_busy_constraints(solver, bruce_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - duration = 990.
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
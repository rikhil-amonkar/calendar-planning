from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
duration = 30  # duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Nicole's preference: Would rather not meet before 16:00.
# Enforce that the meeting must start no earlier than 16:00 (960 minutes)
solver.add(start >= 960)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Judy's busy intervals: Judy is free the entire day.
judy_busy = []
add_busy_constraints(solver, judy_busy)

# Nicole's busy intervals (in minutes):
# 9:00 to 10:00  -> [540, 600)
# 10:30 to 16:30 -> [630, 990)
nicole_busy = [
    (540, 600),
    (630, 990)
]
add_busy_constraints(solver, nicole_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - duration = 1020 - 30 = 990 minutes.
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
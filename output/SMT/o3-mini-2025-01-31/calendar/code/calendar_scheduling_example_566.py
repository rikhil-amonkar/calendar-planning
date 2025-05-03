from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Roy's busy intervals (in minutes):
# 9:00 to 10:30   --> [540, 630)
# 11:30 to 12:30  --> [690, 750)
# 16:00 to 16:30  --> [960, 990)
roy_busy = [
    (540, 630),
    (690, 750),
    (960, 990)
]
add_busy_constraints(solver, roy_busy)

# Debra's busy intervals (in minutes):
# 9:00 to 9:30    --> [540, 570)
# 10:00 to 15:30  --> [600, 930)
# 16:00 to 17:00  --> [960, 1020)
debra_busy = [
    (540, 570),
    (600, 930),
    (960, 1020)
]
add_busy_constraints(solver, debra_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start is 1020 - duration = 990.
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
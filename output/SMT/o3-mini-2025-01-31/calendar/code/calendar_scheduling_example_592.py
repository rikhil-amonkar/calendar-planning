from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Katherine's busy intervals (in minutes since midnight):
# 10:00 to 11:00 -> [600, 660)
katherine_busy = [(600, 660)]
add_busy_constraints(solver, katherine_busy)

# Alexander's busy intervals (in minutes since midnight):
# 9:00 to 11:00  -> [540, 660)
# 12:00 to 17:00 -> [720, 1020)
alexander_busy = [
    (540, 660),
    (720, 1020)
]
add_busy_constraints(solver, alexander_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is such that start + duration <= 1020, i.e., start <= 1020 - duration.
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
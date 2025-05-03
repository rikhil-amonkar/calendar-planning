from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours constraint: Meeting must be between 9:00 (540) and 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Donna prefers to avoid meetings after 10:30.
# Therefore, the meeting must finish by 10:30 (630 minutes).
solver.add(start + duration <= 630)

# Helper function to add constraints that avoid busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Sophia's busy intervals (in minutes since midnight):
# 9:30 to 12:00   -> [570, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:30 to 16:30  -> [870, 990)
sophia_busy = [
    (570, 720),
    (750, 780),
    (870, 990)
]
add_busy_constraints(solver, sophia_busy)

# Donna is free the entire day so no busy intervals for her.

# Search for the earliest valid meeting time.
found = False
# With the constraint that the meeting must finish by 10:30 (630 minutes),
# the latest possible start time is 630 - 30 = 600.
for t in range(540, 601):
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
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Christine's busy intervals (in minutes):
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
christine_busy = [
    (720, 750),
    (780, 810)
]
add_busy_constraints(solver, christine_busy)

# Richard's busy intervals (in minutes):
# 9:00 to 12:00   -> [540, 720)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
richard_busy = [
    (540, 720),
    (780, 810),
    (840, 870),
    (930, 960),
    (990, 1020)
]
add_busy_constraints(solver, richard_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - duration = 960.
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
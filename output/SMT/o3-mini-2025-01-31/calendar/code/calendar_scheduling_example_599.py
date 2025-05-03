from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes);
# thus, start must be at least 540 and the meeting must finish by 1020.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Judith's busy intervals (in minutes since midnight):
# 12:00 to 14:30 -> [720, 870)
# 15:30 to 16:00 -> [930, 960)
judith_busy = [
    (720, 870),
    (930, 960)
]
add_busy_constraints(solver, judith_busy)

# Mason's busy intervals (in minutes since midnight):
# 9:30 to 11:00   -> [570, 660)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
mason_busy = [
    (570, 660),
    (750, 810),
    (840, 870),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, mason_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - duration = 1020 - 60 = 960.
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
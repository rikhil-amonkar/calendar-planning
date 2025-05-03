from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either finish before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Marilyn is free the entire day, so no busy intervals for her.

# Benjamin's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
benjamin_busy = [
    (540, 600),
    (630, 720),
    (810, 870),
    (900, 960),
    (990, 1020)
]
add_busy_constraints(solver, benjamin_busy)

# Search for the earliest valid meeting time.
found = False
# Latest possible start time: 1020 - 60 = 960.
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
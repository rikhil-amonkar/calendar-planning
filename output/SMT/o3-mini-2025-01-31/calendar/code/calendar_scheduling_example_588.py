from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Define work hours: between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Kimberly's busy intervals (in minutes since midnight):
# 9:00 to 9:30    -> [540, 570)
# 13:30 to 14:00  -> [810, 840)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
kimberly_busy = [
    (540, 570),
    (810, 840),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, kimberly_busy)

# Eric's busy intervals (in minutes since midnight):
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 12:30  -> [600, 750)
# 13:00 to 15:30  -> [780, 930)
# 16:30 to 17:00  -> [990, 1020)
eric_busy = [
    (540, 570),
    (600, 750),
    (780, 930),
    (990, 1020)
]
add_busy_constraints(solver, eric_busy)

# Search for the earliest possible valid meeting time.
found = False
# Latest start time is such that start + duration <= 1020, hence start <= 1020 - 60 = 960.
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
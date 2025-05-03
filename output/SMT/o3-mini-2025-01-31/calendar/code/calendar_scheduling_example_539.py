from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540) to 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Andrea's preference: would rather not meet after 12:30
# This implies the meeting must finish by 12:30 (which is 750 minutes).
solver.add(start + duration <= 750)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # enforce that the meeting [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Andrea's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
andrea_busy = [
    (600, 630),
    (690, 720)
]
add_busy_constraints(solver, andrea_busy)

# Abigail's busy intervals (in minutes):
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 14:00  -> [750, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:30 to 17:00  -> [990, 1020)
abigail_busy = [
    (540, 720),
    (750, 840),
    (870, 930),
    (990, 1020)
]
add_busy_constraints(solver, abigail_busy)

# Search for the earliest valid meeting time
found = False
# The latest possible start is 1020 - 30 = 990.
# But note Andrea's preference further restricts meeting to finish by 750.
# So effective range to search for is 540 to 750-duration (750-30=720).
for t in range(540, 721):
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
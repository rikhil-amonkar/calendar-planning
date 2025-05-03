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
    # For each busy interval [b_start, b_end), ensure that the meeting
    # [start, start + duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# James's busy intervals (in minutes):
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
james_busy = [
    (690, 720),
    (870, 900)
]
add_busy_constraints(solver, james_busy)

# John's busy intervals (in minutes):
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 16:30 -> [870, 990)
john_busy = [
    (570, 660),
    (690, 720),
    (750, 810),
    (870, 990)
]
add_busy_constraints(solver, john_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - 60 = 960.
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
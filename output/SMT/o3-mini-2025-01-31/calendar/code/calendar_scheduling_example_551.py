from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Daniel's preference: would rather not meet on Monday after 10:00.
# We interpret this as the meeting must finish by 10:00 (i.e., start + duration <= 600).
solver.add(start + duration <= 600)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Daniel's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 16:00 -> [870, 960)
daniel_busy = [
    (600, 630),
    (690, 720),
    (750, 780),
    (870, 960)
]
add_busy_constraints(solver, daniel_busy)

# Anna's busy intervals (in minutes):
# 9:00 to 9:30  -> [540, 570)
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 17:00 -> [750, 1020)
anna_busy = [
    (540, 570),
    (600, 720),
    (750, 1020)
]
add_busy_constraints(solver, anna_busy)

# Search for the earliest valid meeting time.
found = False
# Given the meeting must end by 10:00 (600), the latest possible start is 600 - 30 = 570.
for t in range(540, 571):  # search from 9:00 (540) to 9:30 (570) inclusive
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
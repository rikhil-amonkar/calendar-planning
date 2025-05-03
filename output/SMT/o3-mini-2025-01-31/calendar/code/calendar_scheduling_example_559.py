from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to enforce no overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # the meeting [start, start+duration) must either end before b_start or start after b_end.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Larry's busy intervals (in minutes):
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:30 -> [870, 930)
larry_busy = [
    (660, 750),
    (780, 810),
    (870, 930)
]
add_busy_constraints(solver, larry_busy)

# James' busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
james_busy = [
    (600, 630),
    (690, 750),
    (810, 840),
    (870, 930),
    (960, 1020)
]
add_busy_constraints(solver, james_busy)

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
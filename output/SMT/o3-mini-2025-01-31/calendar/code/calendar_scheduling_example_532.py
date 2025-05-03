from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint from Helen:
# Helen would rather not meet on Monday after 13:30.
# Therefore, the meeting must finish by 13:30 (which is 810 minutes).
solver.add(start + duration <= 810)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Theresa has no meetings, so no busy intervals for her.

# Helen's busy intervals (in minutes):
# 9:30 to 13:00   -> [570, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 17:00  -> [930, 1020)
helen_busy = [
    (570, 780),
    (810, 840),
    (870, 900),
    (930, 1020)
]
add_busy_constraints(solver, helen_busy)

# Search for the earliest valid meeting time.
found = False
# With the additional constraint that start + duration <= 810, the latest possible start time is 810 - 30 = 780.
for t in range(540, 781):
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
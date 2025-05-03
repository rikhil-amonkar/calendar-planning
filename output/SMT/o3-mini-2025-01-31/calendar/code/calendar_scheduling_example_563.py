from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Alexis does not want to meet before 13:30 (810 minutes)
solver.add(start >= 810)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before b_start
        # or begin after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Andrew's busy intervals (in minutes):
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 15:00 -> [810, 900)
andrew_busy = [
    (750, 780),
    (810, 900)
]
add_busy_constraints(solver, andrew_busy)

# Alexis' busy intervals (in minutes):
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 14:00 -> [720, 840)
# 14:30 to 16:00 -> [870, 960)
alexis_busy = [
    (630, 660),
    (720, 840),
    (870, 960)
]
add_busy_constraints(solver, alexis_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start is 1020 - duration = 960.
# Given Alexis's preference and busy interval, the meeting start must be >= max(810, 840)=840.
for t in range(840, 961):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        solver.pop()
        found = True
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
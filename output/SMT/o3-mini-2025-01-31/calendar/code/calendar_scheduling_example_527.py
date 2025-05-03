from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint from Megan:
# Megan does not want to meet on Monday after 11:00.
# This implies that the meeting must finish by 11:00 (11:00 is 660 minutes)
solver.add(start + duration <= 660)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Wayne's busy intervals:
# Wayne has no meetings the whole day.
wayne_busy = []
add_busy_constraints(solver, wayne_busy)

# Megan's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 14:00 -> [600, 840)
# 14:30 to 17:00 -> [870, 1020)
megan_busy = [
    (540, 570),
    (600, 840),
    (870, 1020)
]
add_busy_constraints(solver, megan_busy)

# Search for the earliest valid meeting time.
found = False
# Given the additional constraint that the meeting must finish by 660,
# the latest possible start time is 660 - duration = 630.
for t in range(540, 631):
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
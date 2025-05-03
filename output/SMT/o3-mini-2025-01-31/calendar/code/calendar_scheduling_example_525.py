from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint: James cannot meet after 14:30.
# This implies the meeting must finish by 14:30, i.e. start + duration <= 870.
solver.add(start + duration <= 870)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting interval [start, start+duration) does not overlap a busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# James's busy intervals (in minutes):
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
james_busy = [
    (570, 600),
    (630, 660)
]
add_busy_constraints(solver, james_busy)

# Lawrence's busy intervals (in minutes):
# 10:00 to 11:00  -> [600, 660)
# 12:00 to 13:00  -> [720, 780)
# 14:00 to 15:00  -> [840, 900)
# 16:00 to 17:00  -> [960, 1020)
lawrence_busy = [
    (600, 660),
    (720, 780),
    (840, 900),
    (960, 1020)
]
add_busy_constraints(solver, lawrence_busy)

# Search for the earliest valid meeting time.
# Given the constraints, the meeting start is between 540 and (1020 - duration) but
# also must satisfy start + duration <= 870. So it makes sense to iterate from 540 to 840.
found = False
for t in range(540, 841):
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
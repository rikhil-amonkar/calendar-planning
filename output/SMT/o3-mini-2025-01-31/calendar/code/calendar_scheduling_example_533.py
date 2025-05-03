from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration of 1 hour
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # enforce that the meeting [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Alexis's busy intervals (in minutes):
# 10:30 to 11:00 -> [630, 660)
# 13:30 to 14:00 -> [810, 840)
alexis_busy = [
    (630, 660),
    (810, 840)
]
add_busy_constraints(solver, alexis_busy)

# Dorothy's busy intervals (in minutes):
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 15:30  -> [840, 930)
# 16:00 to 17:00  -> [960, 1020)
dorothy_busy = [
    (570, 600),
    (630, 690),
    (750, 810),
    (840, 930),
    (960, 1020)
]
add_busy_constraints(solver, dorothy_busy)

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
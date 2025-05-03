from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration of 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to fall within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Brandon is free the entire day, so no busy intervals for Brandon.

# Robert's busy intervals (in minutes):
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 14:00  -> [720, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 16:30  -> [960, 990)
robert_busy = [
    (540, 690),
    (720, 840),
    (870, 930),
    (960, 990)
]
add_busy_constraints(solver, robert_busy)

# The group wants the meeting at the earliest availability.
found = False
# The latest possible start time is 1020 - 30 = 990 minutes.
for t in range(540, 991):
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
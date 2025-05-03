from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint for Anthony:
# Anthony does not want to meet on Monday after 15:30.
# That means the meeting must finish by or before 15:30 (which is 930 minutes).
solver.add(start + duration <= 930)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Anthony's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:30 to 16:30  -> [930, 990)
anthony_busy = [
    (540, 600),
    (750, 780),
    (810, 840),
    (930, 990)
]
add_busy_constraints(solver, anthony_busy)

# Joshua's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:30 to 16:30 -> [930, 990)
joshua_busy = [
    (540, 570),
    (660, 750),
    (780, 840),
    (930, 990)
]
add_busy_constraints(solver, joshua_busy)

# Search for the earliest valid meeting time.
found = False
# Because of the constraint start + duration <= 930,
# the latest valid start time is 930 - duration = 900.
for t in range(540, 901):
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
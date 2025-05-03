from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # enforce that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Kayla's busy intervals in minutes:
# 10:00 to 10:30 -> [600, 630)
# 14:30 to 16:00 -> [870, 960)
kayla_busy = [
    (600, 630),
    (870, 960)
]
add_busy_constraints(solver, kayla_busy)

# Rebecca's busy intervals in minutes:
# 9:00 to 13:00   -> [540, 780)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:00  -> [930, 960)
rebecca_busy = [
    (540, 780),
    (810, 900),
    (930, 960)
]
add_busy_constraints(solver, rebecca_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start is 1020 - duration = 1020 - 60 = 960.
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
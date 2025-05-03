from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters
duration = 60  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: 9:00 (540) to 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Judith's busy intervals in minutes:
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 14:30 -> [840, 870)
judith_busy = [
    (690, 720),
    (840, 870)
]
add_busy_constraints(solver, judith_busy)

# Terry's busy intervals in minutes:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 16:00 -> [870, 960)
terry_busy = [
    (540, 570),
    (660, 750),
    (780, 810),
    (870, 960)
]
add_busy_constraints(solver, terry_busy)

# Search for the earliest valid meeting time:
found = False
# Latest possible start: 1020 - 60 = 960.
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
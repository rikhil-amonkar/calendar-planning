from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlapping busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Carol's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 17:00 -> [930,1020)
carol_busy = [(600, 660), (870, 900), (930, 1020)]
add_busy_constraints(solver, carol_busy)

# Mark's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 17:00 -> [630,1020)
mark_busy = [(570, 600), (630, 1020)]
add_busy_constraints(solver, mark_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# The meeting can start as early as 9:00 (540 minutes) and must finish by 17:00.
for t in range(540, 1020 - duration + 1):
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
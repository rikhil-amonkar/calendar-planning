from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Albert's preference: Cannot meet after 11:00.
# This means the meeting must finish by 11:00 (660 minutes).
solver.add(start + duration <= 660)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Deborah's busy intervals: Deborah is free the entire day.
deborah_busy = []
add_busy_constraints(solver, deborah_busy)

# Albert's busy intervals (in minutes):
# 9:00 to 10:00 -> [540, 600)
# 10:30 to 12:00 -> [630, 720)
# 15:00 to 16:30 -> [900, 990)
albert_busy = [
    (540, 600),
    (630, 720),
    (900, 990)
]
add_busy_constraints(solver, albert_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is given by work hours, and 
# also meeting must finish by 11:00, so t must satisfy t + duration <= 660.
# Therefore, t can be at most 660 - duration = 630.
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
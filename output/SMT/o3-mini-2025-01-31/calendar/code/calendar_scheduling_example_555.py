from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Evelyn's constraint: does not want to meet on Monday after 13:00.
# We interpret this as the meeting must finish by 13:00 (780 minutes).
solver.add(start + duration <= 780)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # the meeting interval [start, start+duration) should not overlap.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Evelyn has no busy intervals besides her preference; nothing to add

# Randy's busy intervals (in minutes):
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 15:30  -> [660, 930)
# 16:00 to 17:00  -> [960, 1020)
randy_busy = [
    (540, 630),
    (660, 930),
    (960, 1020)
]
add_busy_constraints(solver, randy_busy)

# Search for the earliest valid meeting time.
found = False
# Because of Evelyn's constraint, the meeting must finish by 780,
# so the latest possible start is 780 - duration = 750.
for t in range(540, 751):
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
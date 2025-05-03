from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Define basic work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Elijah's preference: he does not want to meet after 15:00.
# This implies the meeting must finish by 15:00, i.e. start + duration <= 900 (since 15:00 is 900 minutes)
solver.add(start + duration <= 900)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) should not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Elijah's busy intervals (in minutes since midnight):
# Busy from 9:00 to 10:00 -> [540, 600)
elijah_busy = [(540, 600)]
add_busy_constraints(solver, elijah_busy)

# Beverly's busy intervals (in minutes since midnight):
# Busy from 9:00 to 12:30  -> [540, 750)
# Busy from 13:30 to 15:30 -> [810, 930)
# Busy from 16:30 to 17:00 -> [990, 1020)
beverly_busy = [
    (540, 750),
    (810, 930),
    (990, 1020)
]
add_busy_constraints(solver, beverly_busy)

# Search for the earliest valid meeting time.
found = False
# Due to the constraint start + duration <= 900, the latest start is 900 - duration = 900 - 30 = 870.
for t in range(540, 871):
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
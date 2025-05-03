from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is one hour (60 minutes)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to ensure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Peter's calendar is wide open, so no busy intervals for him.

# Randy's busy intervals (in minutes):
# 9:00 to 12:30 -> [540, 750)
# 13:30 to 17:00 -> [810, 1020)
randy_busy = [(540, 750), (810, 1020)]
add_busy_constraints(solver, randy_busy)

# Search for the earliest valid one-hour meeting time.
found = False
# The meeting must finish by 1020, so the latest start time is 1020 - 60 = 960.
for t in range(540, 960 + 1):
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
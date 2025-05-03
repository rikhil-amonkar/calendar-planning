from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: Meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Martha cannot meet after 11:00.
# This means the meeting must finish by 11:00 (660 minutes).
solver.add(start + duration <= 660)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Roger is free all day, so no busy intervals are needed for him.

# Martha's busy intervals (in minutes since midnight):
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 13:30  -> [690, 810)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
martha_busy = [
    (570, 660),
    (690, 810),
    (900, 930),
    (960, 1020)
]
# Given that the meeting must finish by 11:00 (660), only the 9:30-11:00 interval is relevant.
add_busy_constraints(solver, martha_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 11:00 (660), so the latest possible start is 660 - 30 = 630.
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
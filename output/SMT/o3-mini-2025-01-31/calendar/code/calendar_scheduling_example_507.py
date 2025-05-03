from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Harold prefers not to meet after 14:00.
# This means the meeting must finish by 14:00 (840 minutes).
solver.add(start + duration <= 840)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Patricia's busy intervals (in minutes):
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
patricia_busy = [(690, 720), (750, 780)]
add_busy_constraints(solver, patricia_busy)

# Harold's busy intervals (in minutes):
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 15:30 -> [810, 930)
# 16:00 to 17:00 -> [960, 1020)
harold_busy = [(570, 630), (690, 720), (750, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, harold_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# The latest possible start is 840 - 30 = 810 due to Harold's preference.
for t in range(540, 810 + 1):
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
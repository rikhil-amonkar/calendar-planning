from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Zachary's busy intervals (in minutes since midnight):
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
zachary_busy = [
    (570, 600),
    (660, 690),
    (810, 870),
    (900, 930),
    (960, 990)
]
add_busy_constraints(solver, zachary_busy)

# Nicole's busy intervals (in minutes since midnight):
# 9:30 to 15:00  -> [570, 900)
# 15:30 to 17:00 -> [930, 1020)
nicole_busy = [
    (570, 900),
    (930, 1020)
]
add_busy_constraints(solver, nicole_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest start is 1020 - 30 = 990.
for t in range(540, 991):
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
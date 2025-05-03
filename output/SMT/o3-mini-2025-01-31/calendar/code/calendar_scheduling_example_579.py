from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helen cannot meet on Monday after 15:00.
# So the meeting must finish by 15:00 (900 minutes).
solver.add(start + duration <= 900)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Christine's busy intervals (in minutes since midnight):
# 11:00 to 11:30  -> [660, 690)
# 15:00 to 15:30  -> [900, 930)
christine_busy = [
    (660, 690),
    (900, 930)
]
add_busy_constraints(solver, christine_busy)

# Helen's busy intervals (in minutes since midnight):
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 16:00  -> [810, 960)
# 16:30 to 17:00  -> [990, 1020)
helen_busy = [
    (570, 630),
    (660, 690),
    (720, 750),
    (810, 960),
    (990, 1020)
]
add_busy_constraints(solver, helen_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 900, so the latest start is 900 - 30 = 870.
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
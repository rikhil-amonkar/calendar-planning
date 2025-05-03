from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Brandon cannot meet before 15:00 (900 minutes).
solver.add(start >= 900)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting's time interval [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Brandon's calendar is wide open (no busy intervals).

# Ralph's busy intervals (in minutes since midnight):
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:30  -> [600, 690)
# 12:30 to 15:00  -> [750, 900)
# 16:00 to 16:30  -> [960, 990)
ralph_busy = [
    (540, 570),
    (600, 690),
    (750, 900),
    (960, 990)
]
add_busy_constraints(solver, ralph_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest start time is 1020 - 60 = 960.
for t in range(900, 961):
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
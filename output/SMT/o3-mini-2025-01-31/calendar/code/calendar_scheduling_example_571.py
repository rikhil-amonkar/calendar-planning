from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: Meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Lori does not want to meet on Monday after 12:30.
# Thus, the meeting should finish by 12:30, which is 750 minutes since midnight.
solver.add(start + duration <= 750)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration) does not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Joseph's busy intervals (in minutes):
# 9:00 to 9:30 -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
joseph_busy = [
    (540, 570),
    (720, 750)
]
add_busy_constraints(solver, joseph_busy)

# Lori's busy intervals (in minutes):
# 9:00 to 11:00 -> [540, 660)
# 11:30 to 12:30 -> [690, 750)
lori_busy = [
    (540, 660),
    (690, 750)
]
add_busy_constraints(solver, lori_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 750, so the latest possible start is 750 - 30 = 720.
for t in range(540, 721):
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
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Jack's constraint: Cannot meet before 16:00 (960 minutes)
solver.add(start >= 960)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must finish before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Scott's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
scott_busy = [
    (600, 630),
    (750, 780),
    (870, 900),
    (960, 990)
]
add_busy_constraints(solver, scott_busy)

# Jack's busy intervals (in minutes):
# 9:00 to 15:00   -> [540, 900)
# 15:30 to 16:30 -> [930, 990)
jack_busy = [
    (540, 900),
    (930, 990)
]
add_busy_constraints(solver, jack_busy)

# Search for the earliest valid meeting time.
found = False
# Meeting must finish by 1020, so latest possible start is 1020 - 30 = 990.
for t in range(960, 991):  # Start from 960 due to Jack's constraint, up to 990 inclusive.
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
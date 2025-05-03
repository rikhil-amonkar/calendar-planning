from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration is one hour
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: The meeting must start no earlier than 9:00 (540 mins) and end by 17:00 (1020 mins)
solver.add(start >= 540, start + duration <= 1020)

# Frances does not want to meet on Monday before 11:00.
# So the meeting must start at or after 11:00 (660 minutes).
solver.add(start >= 660)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Robert's busy intervals (in minutes):
# 10:30 to 11:00 -> [630, 660)
# 15:00 to 15:30 -> [900, 930)
robert_busy = [
    (630, 660),
    (900, 930)
]
add_busy_constraints(solver, robert_busy)

# Frances's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:30 -> [780, 870)
# 15:30 to 17:00 -> [930, 1020)
frances_busy = [
    (540, 570),
    (660, 690),
    (780, 870),
    (930, 1020)
]
add_busy_constraints(solver, frances_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - 60 = 960.
# Also, meeting start must be at least 660.
for t in range(660, 961):
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
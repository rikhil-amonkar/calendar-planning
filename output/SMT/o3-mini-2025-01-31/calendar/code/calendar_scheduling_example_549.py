from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Carl's preference: "rather not meet on Monday after 10:30"
# We interpret this as the meeting must finish by 10:30 (i.e., start + duration <= 630)
solver.add(start + duration <= 630)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Carl's busy intervals (in minutes):
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
carl_busy = [
    (750, 780),
    (870, 900),
    (930, 960),
    (990, 1020)
]
add_busy_constraints(solver, carl_busy)

# Russell's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
russell_busy = [
    (540, 570),
    (600, 630),
    (660, 690),
    (720, 810),
    (870, 900),
    (930, 960)
]
add_busy_constraints(solver, russell_busy)

# Search for the earliest valid meeting time.
# Due to the preference (meeting_end <= 10:30), the meeting start must be <= 600.
found = False
for t in range(540, 601):
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
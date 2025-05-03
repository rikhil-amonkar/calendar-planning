from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration is one hour
start = Int("start")  # meeting start time in minutes since midnight

# Define work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Julie would rather not meet on Monday before 13:30.
# Thus, the meeting should start at or after 13:30 (810 minutes).
solver.add(start >= 810)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Julie's busy intervals (in minutes):
# 9:00 to 9:30  -> [540, 570)
# 12:00 to 12:30 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
julie_busy = [
    (540, 570),
    (720, 780),
    (810, 840),
    (900, 930)
]
add_busy_constraints(solver, julie_busy)

# Catherine's busy intervals (in minutes):
# 9:00 to 10:30  -> [540, 630)
# 13:30 to 16:00 -> [810, 960)
catherine_busy = [
    (540, 630),
    (810, 960)
]
add_busy_constraints(solver, catherine_busy)

# Search for the earliest valid meeting time.
found = False

# The meeting must finish by 17:00 (1020), so the latest possible start is 1020 - 60 = 960.
for t in range(810, 961):
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
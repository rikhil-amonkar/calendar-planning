from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Define work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Deborah does not want to meet on Monday after 12:00.
# Therefore, the meeting must finish by 12:00 (720 minutes).
solver.add(start + duration <= 720)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) should not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Deborah's busy intervals (in minutes since midnight):
# 9:00 to 10:00    -> [540, 600)
# 13:00 to 13:30   -> [780, 810)
# 15:00 to 16:00   -> [900, 960)
# 16:30 to 17:00   -> [990, 1020)
deborah_busy = [
    (540, 600),
    (780, 810),
    (900, 960),
    (990, 1020)
]
add_busy_constraints(solver, deborah_busy)

# Theresa's busy intervals (in minutes since midnight):
# 9:00 to 11:00    -> [540, 660)
# 11:30 to 12:00   -> [690, 720)
# 12:30 to 17:00   -> [750, 1020)
theresa_busy = [
    (540, 660),
    (690, 720),
    (750, 1020)
]
add_busy_constraints(solver, theresa_busy)

# We search for the earliest valid meeting time.
found = False
# The latest possible start is such that start+duration <= 720 (due to Deborah's preference),
# meaning start <= 720 - 30 = 690.
for t in range(540, 691):
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
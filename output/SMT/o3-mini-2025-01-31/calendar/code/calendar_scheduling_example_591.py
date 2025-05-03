from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Define work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Kenneth doesn't want to meet before 13:00.
# 13:00 in minutes is 780.
solver.add(start >= 780)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Kenneth's busy intervals (in minutes since midnight):
# 9:00 to 9:30    -> [540, 570)
# 11:00 to 11:30  -> [660, 690)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
kenneth_busy = [
    (540, 570),
    (660, 690),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, kenneth_busy)

# Melissa's busy intervals (in minutes since midnight):
# 10:30 to 13:00 -> [630, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:30 -> [930, 990)
melissa_busy = [
    (630, 780),
    (840, 870),
    (930, 990)
]
add_busy_constraints(solver, melissa_busy)

# Search for the earliest valid meeting time.
found = False
# Latest possible start time is such that start + duration <= 1020, hence start <= 1020 - 60 = 960.
for t in range(780, 961):
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
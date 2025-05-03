from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration is one hour
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Virginia's busy intervals (in minutes since midnight):
# 9:30 to 10:30   -> [570, 630)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:30 to 16:30  -> [930, 990)
virginia_busy = [
    (570, 630),
    (750, 780),
    (810, 840),
    (930, 990)
]
add_busy_constraints(solver, virginia_busy)

# Billy's busy intervals (in minutes since midnight):
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 13:00  -> [690, 780)
# 15:00 to 16:00  -> [900, 960)
billy_busy = [
    (570, 660),
    (690, 780),
    (900, 960)
]
add_busy_constraints(solver, billy_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest start is 1020 - 60 = 960.
for t in range(540, 961):
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
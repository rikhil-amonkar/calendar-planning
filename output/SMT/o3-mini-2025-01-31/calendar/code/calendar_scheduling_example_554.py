from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # add a constraint ensuring the meeting interval [start, start+duration)
    # does not overlap with the busy interval.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Theresa's busy intervals (in minutes):
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
theresa_busy = [
    (630, 660),
    (690, 720),
    (750, 810),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, theresa_busy)

# Frances' busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 15:00 -> [630, 900)
# 15:30 to 16:30 -> [930, 990)
frances_busy = [
    (540, 570),
    (630, 900),
    (930, 990)
]
add_busy_constraints(solver, frances_busy)

# Search for the earliest valid meeting time.
found = False
# We require start such that start >= 540 and start+duration <=1020,
# hence start can be at most 1020 - 60 = 960.
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
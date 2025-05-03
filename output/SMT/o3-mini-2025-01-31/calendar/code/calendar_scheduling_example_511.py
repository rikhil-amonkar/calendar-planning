from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Scott cannot meet after 11:30, so the meeting must finish by or before 11:30.
# That is, start + duration <= 690 (since 11:30 is 690 minutes).
solver.add(start + duration <= 690)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start + duration) must not overlap with busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Barbara's busy intervals (in minutes):
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
barbara_busy = [(810, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, barbara_busy)

# Scott's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 16:00 -> [900, 960)
scott_busy = [(540, 570), (690, 720), (750, 870), (900, 960)]
add_busy_constraints(solver, scott_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# Scott's constraint forces meeting start t such that t+30 <= 690, i.e., t <= 660.
for t in range(540, 661):
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
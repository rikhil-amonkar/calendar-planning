from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is one hour (60 minutes)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start + duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Wayne's busy intervals (in minutes):
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 15:30 -> [900, 930)
wayne_busy = [(660, 720), (780, 810), (900, 930)]
add_busy_constraints(solver, wayne_busy)

# Laura's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 17:00  -> [630, 1020)
laura_busy = [(540, 570), (630, 1020)]
add_busy_constraints(solver, laura_busy)

# Search for the earliest valid one-hour meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - 60 = 960.
for t in range(540, 960 + 1):
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
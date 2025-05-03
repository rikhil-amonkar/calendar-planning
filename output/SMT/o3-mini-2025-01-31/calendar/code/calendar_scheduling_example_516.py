from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Sophia's calendar is free, so no busy intervals for her.

# Jesse's busy intervals (in minutes):
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 14:30  -> [720, 870)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
jesse_busy = [(540, 690), (720, 870), (930, 960), (990, 1020)]

# Helper function to add busy interval constraints.
def add_busy_constraints(s, busy_intervals):
    for (b_start, b_end) in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        s.add(Or(start + duration <= b_start, start >= b_end))

add_busy_constraints(solver, jesse_busy)

# Search for the earliest valid 60-minute meeting time.
found = False
# Meeting end must be <= 1020, so the latest start is 1020 - 60 = 960.
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
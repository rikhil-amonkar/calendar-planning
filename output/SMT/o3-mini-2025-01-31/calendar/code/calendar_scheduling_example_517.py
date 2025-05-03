from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Carol cannot meet before 14:30 (which is 870 minutes).
solver.add(start >= 870)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Carol is free the whole day, so no busy intervals for her.

# Frank's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 16:00  -> [870, 960)
frank_busy = [
    (540, 600),
    (690, 720),
    (750, 780),
    (810, 840),
    (870, 960)
]
add_busy_constraints(solver, frank_busy)

# Search for the earliest valid 60-minute meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - 60 = 960.
# Also note, Carol's constraint means start >= 870.
for t in range(870, 961):
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
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Mark cannot meet before 15:30.
# 15:30 is 930 minutes, so the meeting must start at or after 930.
solver.add(start >= 930)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start + duration) must not overlap with 
        # the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Pamela has no meetings, so no busy intervals for her.

# Mark's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
mark_busy = [
    (540, 570), (600, 630), (660, 690), (720, 750),
    (840, 870), (900, 930), (960, 1020)
]
add_busy_constraints(solver, mark_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - 30 = 990.
for t in range(930, 991):  # starting from 930 due to Mark's constraint
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
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Daniel's busy intervals (times in minutes since midnight):
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
daniel_busy = [
    (570, 600),
    (660, 690),
    (780, 840),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, daniel_busy)

# Christopher's busy intervals:
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
christopher_busy = [
    (570, 660),
    (690, 750),
    (810, 840),
    (900, 930),
    (960, 990)
]
add_busy_constraints(solver, christopher_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - duration = 1020 - 60 = 960
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
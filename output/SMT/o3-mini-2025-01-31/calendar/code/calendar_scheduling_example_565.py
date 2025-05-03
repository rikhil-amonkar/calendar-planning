from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # half an hour meeting
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540) to 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Joe would rather not meet after 13:30.
# To respect this preference, we require the meeting to finish by 13:30 (810 minutes).
solver.add(start + duration <= 810)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Joe's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:30 -> [870, 930)
joe_busy = [
    (540, 570),
    (600, 630),
    (750, 780),
    (810, 840),
    (870, 930)
]
add_busy_constraints(solver, joe_busy)

# Elijah's busy intervals (in minutes):
# 9:00 to 13:00   -> [540, 780)
# 13:30 to 16:00  -> [810, 960)
# 16:30 to 17:00  -> [990, 1020)
elijah_busy = [
    (540, 780),
    (810, 960),
    (990, 1020)
]
add_busy_constraints(solver, elijah_busy)

# Search for the earliest valid meeting time.
found = False
# Since meeting must finish by 13:30, the latest possible start is 13:00 (780) because 780+30 = 810.
for t in range(540, 781): 
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
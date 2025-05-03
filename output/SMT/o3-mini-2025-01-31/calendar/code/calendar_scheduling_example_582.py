from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540) and 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Ann cannot meet on Monday before 15:00, i.e., meeting must start at or after 15:00 (900 minutes)
solver.add(start >= 900)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting time [start, start+duration) does not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Olivia's busy intervals (in minutes since midnight):
#  9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 13:00 to 14:00  -> [780, 840)
# 15:30 to 16:30  -> [930, 990)
olivia_busy = [
    (570, 600),
    (630, 660),
    (780, 840),
    (930, 990)
]
add_busy_constraints(solver, olivia_busy)

# Ann's busy intervals (in minutes since midnight):
#  9:00 to 9:30   -> [540, 570)
# 11:00 to 13:00  -> [660, 780)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 15:30  -> [900, 930)
ann_busy = [
    (540, 570),
    (660, 780),
    (810, 870),
    (900, 930)
]
add_busy_constraints(solver, ann_busy)

# Search for the earliest valid meeting time.
found = False
# Meeting must finish by 1020, so the latest start time is 1020 - 30 = 990.
for t in range(900, 991):
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
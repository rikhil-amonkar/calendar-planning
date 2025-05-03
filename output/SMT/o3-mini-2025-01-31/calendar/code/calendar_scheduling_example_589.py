from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Paul's preference: do not meet on Monday after 9:30.
# This implies the meeting must finish by 9:30 (570 minutes).
solver.add(start + duration <= 570)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting interval [start, start+duration) does NOT overlap with each busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Laura's busy intervals in minutes since midnight:
# 11:30 to 12:30  -> [690, 750)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 16:30  -> [960, 990)
laura_busy = [
    (690, 750),
    (870, 900),
    (960, 990)
]
add_busy_constraints(solver, laura_busy)

# Paul's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 14:30  -> [660, 870)
# 15:00 to 17:00  -> [900, 1020)
paul_busy = [
    (570, 600),
    (660, 870),
    (900, 1020)
]
add_busy_constraints(solver, paul_busy)

# Search for the earliest valid meeting time.
found = False
# Given the extra constraint (meeting must finish by 570), the start time must be in [540, 540] only.
# However, we'll use a loop over the possible start times for a general solution.
for t in range(540, 571 - duration):  # ensure t+duration <= 570, so t in [540, 540]
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
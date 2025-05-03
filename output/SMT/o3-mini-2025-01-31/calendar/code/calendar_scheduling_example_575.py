from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Stephanie would rather not meet on Monday after 13:00,
# so the meeting must finish by 13:00 (780 minutes).
solver.add(start + duration <= 780)

# Helper function to add constraints ensuring the meeting doesn't overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) does NOT overlap
        # with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Stephanie's busy intervals (in minutes since midnight):
# 11:00 to 11:30 -> [660, 690)
# 16:30 to 17:00 -> [990, 1020)
stephanie_busy = [
    (660, 690),
    (990, 1020)
]
add_busy_constraints(solver, stephanie_busy)

# Samuel's busy intervals (in minutes since midnight):
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 15:30  -> [840, 930)
# 16:30 to 17:00  -> [990, 1020)
samuel_busy = [
    (540, 600),
    (630, 660),
    (690, 750),
    (780, 810),
    (840, 930),
    (990, 1020)
]
add_busy_constraints(solver, samuel_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish no later than 780 minutes, so the latest start is 780 - 30 = 750.
for t in range(540, 751):
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
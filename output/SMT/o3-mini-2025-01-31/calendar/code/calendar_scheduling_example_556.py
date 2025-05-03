from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Deborah's preference: avoid meetings on Monday after 15:00.
# We'll interpret this as the meeting must finish by 15:00 (i.e., start + duration <= 900).
solver.add(start + duration <= 900)

# Helper function: add constraints to ensure the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting can be scheduled if it ends before the busy interval starts,
        # or if it starts after the busy interval ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Eric's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 14:00  -> [750, 840)
eric_busy = [
    (540, 600),
    (690, 720),
    (750, 840)
]
add_busy_constraints(solver, eric_busy)

# Deborah's busy intervals (in minutes):
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 15:30  -> [900, 930)
deborah_busy = [
    (540, 630),
    (660, 690),
    (720, 750),
    (810, 870),
    (900, 930)
]
add_busy_constraints(solver, deborah_busy)

# Search for the earliest valid meeting time.
found = False
# Since Deborah's meeting must finish by 15:00 (900 min), the latest start is 900 - duration = 870.
for t in range(540, 871):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        solver.pop()
        found = True
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
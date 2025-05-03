from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Monday work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration of the meeting: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping with busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap with a busy interval [bs, be)
        s.add(Or(start + duration <= bs, start >= be))

# Evelyn is free the entire day: no constraints needed.

# Patrick's busy intervals:
#   12:00 to 13:00 → [720, 780)
#   15:00 to 15:30 → [900, 930)
#   16:30 to 17:00 → [990, 1020)
patrick_busy = [(720, 780), (900, 930), (990, 1020)]
add_busy_constraints(solver, patrick_busy)

# Anthony's busy intervals:
#   9:30 to 10:30  → [570, 630)
#   12:00 to 13:00 → [720, 780)
#   13:30 to 14:00 → [810, 840)
#   16:30 to 17:00 → [990, 1020)
anthony_busy = [(570, 630), (720, 780), (810, 840), (990, 1020)]
add_busy_constraints(solver, anthony_busy)

# Aaron's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 10:30 → [600, 630)
#   11:30 to 12:00 → [690, 720)
#   12:30 to 13:30 → [750, 810)
#   14:30 to 15:30 → [870, 930)
#   16:30 to 17:00 → [990, 1020)
aaron_busy = [(540, 570), (600, 630), (690, 720), (750, 810), (870, 930), (990, 1020)]
add_busy_constraints(solver, aaron_busy)

# Abigail's busy intervals:
#   9:00 to 11:00   → [540, 660)
#   11:30 to 12:00  → [690, 720)
#   12:30 to 14:00  → [750, 840)
#   14:30 to 16:00  → [870, 960)
#   16:30 to 17:00  → [990, 1020)
abigail_busy = [(540, 660), (690, 720), (750, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, abigail_busy)

# Vincent's busy intervals:
#   9:00 to 10:30  → [540, 630)
#   11:30 to 12:00 → [690, 720)
#   14:00 to 17:00 → [840, 1020)
vincent_busy = [(540, 630), (690, 720), (840, 1020)]
add_busy_constraints(solver, vincent_busy)

# Search for the earliest valid meeting start time.
found = False
# Try candidate start times from 9:00 (540) onward.
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
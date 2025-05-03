from z3 import Solver, Int, Or, sat

# Create a new Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlapping constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bstart, bend in busy_intervals:
        # The meeting [start, start+duration) must finish before the busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bstart, start >= bend))

# Gregory's busy intervals:
# 14:00 to 17:00 -> [840, 1020)
gregory_busy = [(840, 1020)]
add_busy_constraints(solver, gregory_busy)

# John has no meetings (free all day).

# Roger is free all day (no constraints).

# Roy's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 14:30 to 15:00 -> [870, 900)
roy_busy = [(630, 660), (870, 900)]
add_busy_constraints(solver, roy_busy)

# Adam's busy intervals:
# 9:00 to 12:30  -> [540, 750)
# 13:30 to 17:00 -> [810, 1020)
adam_busy = [(540, 750), (810, 1020)]
add_busy_constraints(solver, adam_busy)

# Judith's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
judith_busy = [(540, 630), (720, 780), (810, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, judith_busy)

# Robert's busy intervals:
# 9:00 to 13:00   -> [540, 780)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 17:00  -> [930, 1020)
robert_busy = [(540, 780), (810, 900), (930, 1020)]
add_busy_constraints(solver, robert_busy)

# Search for the earliest available meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
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
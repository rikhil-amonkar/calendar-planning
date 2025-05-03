from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a given set of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) should either end before the busy interval starts,
        # or start after it ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Jack has no meetings (free all day), so no constraints needed.

# Jacob's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 13:30 to 14:00 -> [810, 840)
jacob_busy = [(570, 600), (810, 840)]
add_busy_constraints(solver, jacob_busy)

# Edward's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
edward_busy = [(540, 570), (600, 630), (690, 720), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, edward_busy)

# Sean is free all day; no constraints needed.

# Lori's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:30 -> [780, 870)
# 15:30 to 16:30 -> [930, 990)
lori_busy = [(600, 630), (660, 690), (720, 750), (780, 870), (930, 990)]
add_busy_constraints(solver, lori_busy)

# Billy's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 12:30  -> [720, 750)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
billy_busy = [(540, 660), (720, 750), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, billy_busy)

# Willie's busy intervals:
# 10:00 to 12:30 -> [600, 750)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:30 -> [870, 990)
willie_busy = [(600, 750), (810, 840), (870, 990)]
add_busy_constraints(solver, willie_busy)

# Search for the earliest available meeting time that satisfies all constraints.
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
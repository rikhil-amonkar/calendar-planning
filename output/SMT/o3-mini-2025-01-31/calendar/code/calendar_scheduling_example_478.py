from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to be completely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before b_start or start after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Kimberly has no meetings, so no constraints.

# Deborah's busy intervals:
# 12:00 to 13:00 -> [720, 780)
# 14:30 to 15:30 -> [870, 930)
deborah_busy = [(720, 780), (870, 930)]
add_busy_constraints(solver, deborah_busy)

# Samuel's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:30 -> [690, 750)
# 15:30 to 16:30 -> [930, 990)
samuel_busy = [(540, 570), (600, 630), (690, 750), (930, 990)]
add_busy_constraints(solver, samuel_busy)

# Lisa's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:30  -> [750, 810)
# 15:30 to 16:30  -> [930, 990)
lisa_busy = [(570, 600), (690, 720), (750, 810), (930, 990)]
add_busy_constraints(solver, lisa_busy)

# Vincent's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 15:30 -> [840, 930)
# 16:00 to 17:00 -> [960, 1020)
vincent_busy = [(570, 630), (660, 720), (750, 780), (840, 930), (960, 1020)]
add_busy_constraints(solver, vincent_busy)

# Julia's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 14:00 -> [660, 840)
# 15:00 to 15:30 -> [900, 930)
julia_busy = [(540, 570), (660, 840), (900, 930)]
add_busy_constraints(solver, julia_busy)

# Judith's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 14:00 -> [750, 840)
# 14:30 to 17:00 -> [870, 1020)
judith_busy = [(540, 570), (600, 630), (660, 720), (750, 840), (870, 1020)]
add_busy_constraints(solver, judith_busy)

# Search for the earliest time slot that meets all constraints.
found = False
for t in range(540, 1020 - duration + 1):  # t ranges from 540 up to 990 inclusive.
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
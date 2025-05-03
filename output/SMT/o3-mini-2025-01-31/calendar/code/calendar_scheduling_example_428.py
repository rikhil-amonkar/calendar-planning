from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must finish before a busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Denise is free the entire day: no constraints needed.

# Amber's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
amber_busy = [(600, 630), (690, 720), (930, 960), (990, 1020)]
add_busy_constraints(solver, amber_busy)

# Charles's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:30  -> [690, 750)
# 13:30 to 15:00  -> [810, 900)
charles_busy = [(570, 600), (690, 750), (810, 900)]
add_busy_constraints(solver, charles_busy)

# Edward's busy intervals:
# 11:30 to 12:30 -> [690, 750)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
edward_busy = [(690, 750), (870, 900), (960, 990)]
add_busy_constraints(solver, edward_busy)

# Richard's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:30 -> [660, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:30 -> [900, 990)
richard_busy = [(540, 570), (660, 750), (840, 870), (900, 990)]
add_busy_constraints(solver, richard_busy)

# Katherine's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 16:00 to 16:30  -> [960, 990)
katherine_busy = [(540, 660), (690, 720), (750, 780), (810, 840), (960, 990)]
add_busy_constraints(solver, katherine_busy)

# Russell's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 16:00  -> [840, 960)
# 16:30 to 17:00  -> [990, 1020)
russell_busy = [(540, 720), (750, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, russell_busy)

# Try all possible start times in the work hours to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
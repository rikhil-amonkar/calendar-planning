from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must finish before the busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Justin's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
justin_busy = [(570, 630), (870, 900), (990, 1020)]
add_busy_constraints(solver, justin_busy)

# Nancy's calendar is wide open, so no constraints.

# Willie's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
willie_busy = [(570, 600), (720, 750), (840, 870), (930, 960)]
add_busy_constraints(solver, willie_busy)

# Alan's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 16:30 to 17:00 -> [990, 1020)
alan_busy = [(570, 600), (750, 780), (810, 840), (990, 1020)]
add_busy_constraints(solver, alan_busy)

# Brian's busy intervals:
# 10:00 to 10:30  -> [600, 630)
# 11:00 to 12:30  -> [660, 750)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 17:00  -> [960, 1020)
brian_busy = [(600, 630), (660, 750), (780, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, brian_busy)

# Lori's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:30 to 16:30  -> [810, 990)
lori_busy = [(570, 660), (690, 720), (810, 990)]
add_busy_constraints(solver, lori_busy)

# Isabella's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:00 -> [870, 960)
# 16:30 to 17:00 -> [990, 1020)
isabella_busy = [(630, 690), (720, 750), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, isabella_busy)

# Try possible meeting start times within work hours.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
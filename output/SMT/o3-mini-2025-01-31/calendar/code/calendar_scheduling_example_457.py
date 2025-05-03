from z3 import Solver, Int, Or, sat

# Create Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to be entirely within work hours
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals:
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must complete before a busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Andrea's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 13:30 to 14:30 -> [810, 870)
andrea_busy = [(570, 630), (810, 870)]
add_busy_constraints(solver, andrea_busy)

# Ruth's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:00 to 15:30 -> [900, 930)
ruth_busy = [(750, 780), (900, 930)]
add_busy_constraints(solver, ruth_busy)

# Steven's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 16:00 -> [900, 960)
steven_busy = [(600, 630), (660, 690), (720, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, steven_busy)

# Grace has no busy intervals.

# Kyle's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
kyle_busy = [(540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, kyle_busy)

# Elijah's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
elijah_busy = [(540, 660), (690, 780), (810, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, elijah_busy)

# Lori's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:30  -> [600, 690)
# 12:00 to 13:30  -> [720, 810)
# 14:00 to 16:00  -> [840, 960)
# 16:30 to 17:00  -> [990, 1020)
lori_busy = [(540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, lori_busy)

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
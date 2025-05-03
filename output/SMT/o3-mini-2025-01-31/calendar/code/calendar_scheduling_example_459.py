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

# Helper function to add constraints ensuring the meeting doesn't overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must finish before the busy interval
        # or start after the busy interval.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Marie's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
marie_busy = [(630, 660), (720, 750), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, marie_busy)

# Roger's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 15:30 -> [840, 930)
roger_busy = [(660, 690), (840, 930)]
add_busy_constraints(solver, roger_busy)

# John's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 15:30 to 16:00 -> [930, 960)
john_busy = [(600, 630), (930, 960)]
add_busy_constraints(solver, john_busy)

# Peter's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 16:30 to 17:00 -> [990, 1020)
peter_busy = [(810, 840), (990, 1020)]
add_busy_constraints(solver, peter_busy)

# Ruth's busy intervals:
# 9:30 to 15:30 -> [570, 930)
# 16:00 to 17:00 -> [960, 1020)
ruth_busy = [(570, 930), (960, 1020)]
add_busy_constraints(solver, ruth_busy)

# James's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 13:00 -> [720, 780)
# 14:30 to 17:00 -> [870, 1020)
james_busy = [(630, 660), (720, 780), (870, 1020)]
add_busy_constraints(solver, james_busy)

# Victoria's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 15:00  -> [750, 900)
# 15:30 to 17:00  -> [930, 1020)
victoria_busy = [(570, 660), (690, 720), (750, 900), (930, 1020)]
add_busy_constraints(solver, victoria_busy)

# Iterate over possible meeting start times within work hours.
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
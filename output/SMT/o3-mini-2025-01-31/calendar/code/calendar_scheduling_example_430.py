from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must begin and end within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting interval [start, start+duration) must end before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jessica's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 16:30 to 17:00 -> [990, 1020)
jessica_busy = [(570, 600), (990, 1020)]
add_busy_constraints(solver, jessica_busy)

# Elijah's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 14:00 to 14:30   -> [840, 870)
# 15:00 to 16:00   -> [900, 960)
elijah_busy = [(570, 600), (840, 870), (900, 960)]
add_busy_constraints(solver, elijah_busy)

# Ann's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 16:30 to 17:00 -> [990, 1020)
ann_busy = [(660, 690), (990, 1020)]
add_busy_constraints(solver, ann_busy)

# Marie is free all day: no constraints.

# Kathryn's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:30  -> [690, 750)
# 14:00 to 15:30  -> [840, 930)
kathryn_busy = [(540, 600), (630, 660), (690, 750), (840, 930)]
add_busy_constraints(solver, kathryn_busy)

# Albert's busy intervals:
# 9:00 to 11:00    -> [540, 660)
# 11:30 to 12:30   -> [690, 750)
# 16:00 to 17:00   -> [960, 1020)
albert_busy = [(540, 660), (690, 750), (960, 1020)]
add_busy_constraints(solver, albert_busy)

# Nicole's busy intervals:
# 10:00 to 11:00   -> [600, 660)
# 12:00 to 12:30   -> [720, 750)
# 14:00 to 15:00   -> [840, 900)
# 15:30 to 17:00   -> [930, 1020)
nicole_busy = [(600, 660), (720, 750), (840, 900), (930, 1020)]
add_busy_constraints(solver, nicole_busy)

# Search through every possible start time within work hours to find a valid meeting slot.
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
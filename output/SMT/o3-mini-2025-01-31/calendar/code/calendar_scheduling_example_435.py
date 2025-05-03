from z3 import Solver, Int, Or, sat

# Create Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval (busy_start, busy_end),
# the meeting [start, start+duration) must either finish before busy_start,
# or start after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Lawrence's busy intervals:
# 10:00 to 10:30   -> [600, 630)
# 13:30 to 14:00   -> [810, 840)
lawrence_busy = [(600, 630), (810, 840)]
add_busy_constraints(solver, lawrence_busy)

# Shirley is free the whole day, no busy intervals.

# Alexander's busy intervals:
# 9:30 to 10:00    -> [570, 600)
# 10:30 to 11:30   -> [630, 690)
# 12:30 to 13:00   -> [750, 780)
alexander_busy = [(570, 600), (630, 690), (750, 780)]
add_busy_constraints(solver, alexander_busy)

# Brian's busy intervals:
# 9:00 to 9:30     -> [540, 570)
# 13:30 to 14:00   -> [810, 840)
brian_busy = [(540, 570), (810, 840)]
add_busy_constraints(solver, brian_busy)

# Kathryn's busy intervals:
# 9:00 to 15:00     -> [540, 900)
# 16:00 to 17:00    -> [960, 1020)
kathryn_busy = [(540, 900), (960, 1020)]
add_busy_constraints(solver, kathryn_busy)

# Aaron's busy intervals:
# 9:00 to 11:00     -> [540, 660)
# 11:30 to 12:30    -> [690, 750)
# 13:00 to 13:30    -> [780, 810)
# 14:00 to 15:00    -> [840, 900)
# 16:00 to 16:30    -> [960, 990)
aaron_busy = [(540, 660), (690, 750), (780, 810), (840, 900), (960, 990)]
add_busy_constraints(solver, aaron_busy)

# Janice's busy intervals:
# 9:00 to 11:30     -> [540, 690)
# 12:00 to 12:30    -> [720, 750)
# 13:00 to 15:00    -> [780, 900)
# 15:30 to 16:00    -> [930, 960)
# 16:30 to 17:00    -> [990, 1020)
janice_busy = [(540, 690), (720, 750), (780, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, janice_busy)

# Iterate over possible start times to find a valid meeting time.
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
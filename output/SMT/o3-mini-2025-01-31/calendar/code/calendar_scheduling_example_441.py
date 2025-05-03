from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start+duration)
# must either finish before busy_start or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Joan's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
joan_busy = [(690, 720), (870, 900)]
add_busy_constraints(solver, joan_busy)

# Megan's busy intervals:
# 9:00 to 10:00 -> [540, 600)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
megan_busy = [(540, 600), (840, 870), (960, 990)]
add_busy_constraints(solver, megan_busy)

# Austin is free the entire day, no constraints needed.

# Betty's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
betty_busy = [(570, 600), (690, 720), (810, 840), (960, 990)]
add_busy_constraints(solver, betty_busy)

# Judith's busy intervals:
# 9:00 to 11:00 -> [540, 660)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 15:00 -> [840, 900)
judith_busy = [(540, 660), (720, 780), (840, 900)]
add_busy_constraints(solver, judith_busy)

# Terry's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
terry_busy = [(570, 600), (690, 750), (780, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, terry_busy)

# Kathryn's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 13:00 -> [690, 780)
# 14:00 to 16:00 -> [840, 960)
# 16:30 to 17:00 -> [990, 1020)
kathryn_busy = [(570, 600), (630, 660), (690, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, kathryn_busy)

# Try to find a valid meeting start time by iterating over possible start times.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}.".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
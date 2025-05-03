from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Ensure the meeting either finishes before the busy interval starts or starts after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Frank's busy intervals:
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
frank_busy = [(660, 720), (750, 780), (840, 870)]
add_busy_constraints(solver, frank_busy)

# Julie's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 16:30 to 17:00 -> [990, 1020)
julie_busy = [(570, 600), (660, 690), (750, 780), (990, 1020)]
add_busy_constraints(solver, julie_busy)

# Donna has no meetings, so no constraints.

# Ronald has no meetings, so no constraints.

# Peter's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
peter_busy = [(570, 630), (660, 690), (720, 780), (810, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, peter_busy)

# Nancy's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 16:00 -> [840, 960)
nancy_busy = [(600, 660), (690, 720), (750, 780), (840, 960)]
add_busy_constraints(solver, nancy_busy)

# Scott's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 12:30 to 13:30 -> [750, 810)
# 15:00 to 16:00 -> [900, 960)
scott_busy = [(570, 690), (750, 810), (900, 960)]
add_busy_constraints(solver, scott_busy)

# Now, iterate over possible start times to find a valid meeting slot.
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
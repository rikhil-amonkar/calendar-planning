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

# Donna would like to avoid meetings before 10:00.
# We interpret this as a hard preference so the meeting must start at or after 10:00 (600 minutes).
solver.add(start >= 600)

# Helper function: add constraints ensuring that the meeting does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting interval [start, start+duration) must finish before a busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Donna's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
donna_busy = [(600, 630), (660, 750), (780, 810), (870, 900)]
add_busy_constraints(solver, donna_busy)

# Albert's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 15:00 -> [810, 900)
# 16:00 to 16:30 -> [960, 990)
albert_busy = [(600, 630), (660, 690), (810, 900), (960, 990)]
add_busy_constraints(solver, albert_busy)

# Jeremy has no meetings so no constraints are added.

# Grace's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 16:30 to 17:00 -> [990, 1020)
grace_busy = [(780, 810), (990, 1020)]
add_busy_constraints(solver, grace_busy)

# Matthew's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 15:00 -> [720, 900)
# 15:30 to 16:30 -> [930, 990)
matthew_busy = [(600, 630), (660, 690), (720, 900), (930, 990)]
add_busy_constraints(solver, matthew_busy)

# Jean's busy intervals:
# 11:00 to 13:30 -> [660, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
jean_busy = [(660, 810), (870, 930), (990, 1020)]
add_busy_constraints(solver, jean_busy)

# Dylan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
dylan_busy = [(540, 570), (600, 630), (690, 720), (750, 780), (810, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, dylan_busy)

# Search for a valid meeting time:
found = False
for t in range(540, 1020 - duration + 1):  # iterate through every possible minute in the work period
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
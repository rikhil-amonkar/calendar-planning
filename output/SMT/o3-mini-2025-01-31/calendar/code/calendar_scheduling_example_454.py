from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Constrain meeting to be entirely inside work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval, ensure that the meeting does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting can either finish before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Sara's busy interval:
# 9:30 to 10:30 -> [570, 630)
sara_busy = [(570, 630)]
add_busy_constraints(solver, sara_busy)

# Ethan's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 16:00 -> [930, 960)
ethan_busy = [(660, 690), (720, 750), (810, 900), (930, 960)]
add_busy_constraints(solver, ethan_busy)

# Stephanie: no busy intervals.

# Hannah's busy intervals:
# 12:30 to 13:30 -> [750, 810)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
hannah_busy = [(750, 810), (930, 960), (990, 1020)]
add_busy_constraints(solver, hannah_busy)

# Kevin's busy intervals:
# 9:00 to 15:00   -> [540, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
kevin_busy = [(540, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, kevin_busy)

# Susan's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 13:30 -> [660, 810)
# 14:30 to 16:00 -> [870, 960)
# 16:30 to 17:00 -> [990, 1020)
susan_busy = [(600, 630), (660, 810), (870, 960), (990, 1020)]
add_busy_constraints(solver, susan_busy)

# Bryan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 15:30 -> [810, 930)
# 16:30 to 17:00 -> [990, 1020)
bryan_busy = [(540, 570), (600, 630), (690, 720), (810, 930), (990, 1020)]
add_busy_constraints(solver, bryan_busy)

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
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}.".format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
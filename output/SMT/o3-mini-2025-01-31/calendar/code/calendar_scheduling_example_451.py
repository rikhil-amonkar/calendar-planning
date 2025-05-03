from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint for Sandra:
# Sandra does not want to meet before 13:30, i.e., meeting start must be >= 13:30 (810 minutes).
solver.add(start >= 810)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end), the meeting must either end before busy_start or start at/after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Judy's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 13:00 -> [720, 780)
# 15:00 to 16:00 -> [900, 960)
judy_busy = [(630, 690), (720, 780), (900, 960)]
add_busy_constraints(solver, judy_busy)

# Jack's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
jack_busy = [(630, 690), (750, 780), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, jack_busy)

# Ronald's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 16:30 to 17:00 -> [990, 1020)
ronald_busy = [(630, 660), (690, 720), (750, 780), (990, 1020)]
add_busy_constraints(solver, ronald_busy)

# Sandra has no busy intervals, but the constraint for no meeting before 13:30 has been added already.

# Ashley's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 13:00 -> [660, 780)
# 13:30 to 16:00 -> [810, 960)
ashley_busy = [(600, 630), (660, 780), (810, 960)]
add_busy_constraints(solver, ashley_busy)

# Heather's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 15:30 -> [810, 930)
# 16:30 to 17:00 -> [990, 1020)
heather_busy = [(540, 570), (600, 690), (720, 750), (810, 930), (990, 1020)]
add_busy_constraints(solver, heather_busy)

# Terry's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 16:00  -> [810, 960)
terry_busy = [(540, 600), (630, 660), (720, 780), (810, 960)]
add_busy_constraints(solver, terry_busy)

# Iterate over possible meeting start times (each minute) within work hours.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    # We have already constrained start >= 810 due to Sandra's preference, so t must be >= 810.
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
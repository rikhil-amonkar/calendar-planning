from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must finish before the busy interval starts 
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Judy's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 16:00 to 16:30 -> [960, 990)
judy_busy = [(780, 810), (960, 990)]
add_busy_constraints(solver, judy_busy)

# Olivia's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 14:30 -> [840, 870)
olivia_busy = [(600, 630), (720, 780), (840, 870)]
add_busy_constraints(solver, olivia_busy)

# Eric is free the entire day, so no constraints.

# Jacqueline's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 15:00 to 15:30 -> [900, 930)
jacqueline_busy = [(600, 630), (900, 930)]
add_busy_constraints(solver, jacqueline_busy)

# Laura's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 10:30 to 12:00   -> [630, 720)
# 13:00 to 13:30   -> [780, 810)
# 14:30 to 15:00   -> [870, 900)
# 15:30 to 17:00   -> [930, 1020)
laura_busy = [(540, 600), (630, 720), (780, 810), (870, 900), (930, 1020)]
add_busy_constraints(solver, laura_busy)

# Tyler's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 11:00 to 11:30   -> [660, 690)
# 12:30 to 13:00   -> [750, 780)
# 14:00 to 14:30   -> [840, 870)
# 15:30 to 17:00   -> [930, 1020)
tyler_busy = [(540, 600), (660, 690), (750, 780), (840, 870), (930, 1020)]
add_busy_constraints(solver, tyler_busy)

# Lisa's busy intervals:
# 9:30 to 10:30    -> [570, 630)
# 11:00 to 11:30   -> [660, 690)
# 12:00 to 12:30   -> [720, 750)
# 13:00 to 13:30   -> [780, 810)
# 14:00 to 14:30   -> [840, 870)
# 16:00 to 17:00   -> [960, 1020)
lisa_busy = [(570, 630), (660, 690), (720, 750), (780, 810), (840, 870), (960, 1020)]
add_busy_constraints(solver, lisa_busy)

# Iterate over possible start times, checking for a valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):  # iterate from 9:00 to latest possible start time
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
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration) 
# must either finish before busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jeffrey's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 13:30 to 14:00 -> [810, 840)
jeffrey_busy = [(630, 660), (810, 840)]
add_busy_constraints(solver, jeffrey_busy)

# Nancy's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
nancy_busy = [(660, 690), (840, 870), (900, 960)]
add_busy_constraints(solver, nancy_busy)

# Jordan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 14:30 -> [810, 870)
jordan_busy = [(540, 570), (690, 720), (810, 870)]
add_busy_constraints(solver, jordan_busy)

# Samantha's busy intervals:
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 16:30 -> [960, 990)
samantha_busy = [(690, 750), (780, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, samantha_busy)

# Jason's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:30 -> [930, 990)
jason_busy = [(540, 630), (660, 690), (720, 750), (810, 840), (930, 990)]
add_busy_constraints(solver, jason_busy)

# Shirley's busy intervals:
# 9:00 to 10:00  -> [540, 600)
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 15:30 -> [810, 930)
# 16:00 to 16:30 -> [960, 990)
shirley_busy = [(540, 600), (630, 660), (720, 780), (810, 930), (960, 990)]
add_busy_constraints(solver, shirley_busy)

# Jessica's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 15:30 -> [720, 930)
jessica_busy = [(570, 630), (660, 690), (720, 930)]
add_busy_constraints(solver, jessica_busy)

# Try to find a valid meeting start time by iterating over each possible minute.
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
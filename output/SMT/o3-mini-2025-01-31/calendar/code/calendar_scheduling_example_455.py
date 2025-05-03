from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting doesn't overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting [start, start+duration) must either finish before the busy period or start after it.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Ryan's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
ryan_busy = [(570, 600), (720, 750), (840, 870), (930, 960)]
add_busy_constraints(solver, ryan_busy)

# Jerry has no meetings. No busy intervals needed.

# Raymond's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 14:30 to 15:00 -> [870, 900)
raymond_busy = [(540, 570), (870, 900)]
add_busy_constraints(solver, raymond_busy)

# Eugene's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:00 to 12:30  -> [720, 750)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
eugene_busy = [(540, 600), (630, 660), (720, 750), (900, 930), (990, 1020)]
add_busy_constraints(solver, eugene_busy)

# Justin's busy intervals:
# 9:30 to 12:30  -> [570, 750)
# 13:00 to 15:30 -> [780, 930)
# 16:30 to 17:00 -> [990, 1020)
justin_busy = [(570, 750), (780, 930), (990, 1020)]
add_busy_constraints(solver, justin_busy)

# Gerald's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 13:00 -> [750, 780)
# 15:00 to 16:00 -> [900, 960)
gerald_busy = [(540, 570), (600, 720), (750, 780), (900, 960)]
add_busy_constraints(solver, gerald_busy)

# Eric's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
eric_busy = [(540, 600), (690, 780), (810, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, eric_busy)

# Iterate over possible meeting start times within working hours.
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
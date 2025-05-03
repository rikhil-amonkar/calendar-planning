from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [busy_start, busy_end), the meeting interval
# [start, start+duration) must either finish at or before busy_start
# or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Joan's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
joan_busy = [(600, 660), (840, 870), (990, 1020)]
add_busy_constraints(solver, joan_busy)

# Sean's busy intervals:
# 12:30 to 13:30 -> [750, 810)
sean_busy = [(750, 810)]
add_busy_constraints(solver, sean_busy)

# Christian's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
christian_busy = [(600, 630), (660, 690), (720, 750), (780, 810), (840, 900)]
add_busy_constraints(solver, christian_busy)

# Jerry is free for the entire day; no busy intervals.

# Jessica's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
jessica_busy = [(600, 660), (690, 780), (810, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, jessica_busy)

# Virginia's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:00 -> [630, 720)
# 13:30 to 15:00 -> [810, 900)
# 16:30 to 17:00 -> [990, 1020)
virginia_busy = [(540, 570), (630, 720), (810, 900), (990, 1020)]
add_busy_constraints(solver, virginia_busy)

# Harold's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 13:00  -> [630, 780)
# 13:30 to 16:00  -> [810, 960)
# 16:30 to 17:00  -> [990, 1020)
harold_busy = [(570, 600), (630, 780), (810, 960), (990, 1020)]
add_busy_constraints(solver, harold_busy)

# Iterate over possible meeting start times.
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
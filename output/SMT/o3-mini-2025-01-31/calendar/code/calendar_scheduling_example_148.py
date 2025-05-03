from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)
# Stephen cannot meet on Monday before 14:00 (840 minutes)
solver.add(start >= 840)

# Helper function: For each busy interval [bs, be),
# ensure the meeting [start, start+duration) does not overlap.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Deborah's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 17:00 -> [960,1020)
deborah_busy = [(750, 780), (810, 840), (960, 1020)]
add_busy_constraints(solver, deborah_busy)

# Samuel's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 15:30 to 16:00 -> [930, 960)
samuel_busy = [(690, 720), (930, 960)]
add_busy_constraints(solver, samuel_busy)

# Betty's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 14:30 -> [750, 870)
# 16:00 to 17:00 -> [960,1020)
betty_busy = [(570, 600), (690, 720), (750, 870), (960, 1020)]
add_busy_constraints(solver, betty_busy)

# Stephen's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 15:00 -> [780, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990,1020)
stephen_busy = [(600, 630), (660, 690), (780, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, stephen_busy)

# Try possible meeting start times from 14:00 (840 minutes) to the latest valid start time (1020 - duration).
solution_found = False
for t in range(840, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        start_hours, start_minutes = divmod(meeting_start, 60)
        end_hours, end_minutes = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hours, start_minutes, end_hours, end_minutes))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
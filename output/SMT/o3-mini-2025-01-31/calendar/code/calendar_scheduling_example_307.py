from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must finish before the busy interval starts or start after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Ronald's calendar is wide open, so no busy intervals.

# Stephen's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   12:00 to 12:30 -> [720, 750)
stephen_busy = [(600, 630), (720, 750)]
add_busy_constraints(solver, stephen_busy)

# Brittany's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   13:30 to 14:00 -> [810, 840)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
brittany_busy = [(660, 690), (810, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, brittany_busy)

# Dorothy's busy intervals:
#   9:00 to 9:30  -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 12:30 -> [660, 750)
#   13:00 to 15:00 -> [780, 900)
#   15:30 to 17:00 -> [930, 1020)
dorothy_busy = [(540, 570), (600, 630), (660, 750), (780, 900), (930, 1020)]
add_busy_constraints(solver, dorothy_busy)

# Rebecca's busy intervals:
#   9:30 to 10:30 -> [570, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 17:00 -> [780, 1020)
rebecca_busy = [(570, 630), (660, 690), (720, 750), (780, 1020)]
add_busy_constraints(solver, rebecca_busy)

# Jordan's busy intervals:
#   9:00 to 9:30  -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 15:00 -> [780, 900)
#   15:30 to 16:30 -> [930, 990)
jordan_busy = [(540, 570), (600, 660), (690, 720), (780, 900), (930, 990)]
add_busy_constraints(solver, jordan_busy)

# Now, search for an earliest valid meeting start time that satisfies all constraints.
found = False

# The start time must be chosen between 540 and 1020-duration (inclusive)
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
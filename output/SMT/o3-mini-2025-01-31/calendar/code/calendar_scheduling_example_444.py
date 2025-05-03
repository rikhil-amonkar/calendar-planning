from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval [busy_start, busy_end),
# the meeting [start, start+duration) must either end before busy_start
# or start after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Abigail's busy intervals:
# 12:00 to 12:30 --> [720, 750)
# 14:30 to 15:00 --> [870, 900)
abigail_busy = [(720, 750), (870, 900)]
add_busy_constraints(solver, abigail_busy)

# Roy's busy intervals:
# 9:30 to 10:30  --> [570, 630)
# 13:30 to 14:00 --> [810, 840)
# 16:30 to 17:00 --> [990, 1020)
roy_busy = [(570, 630), (810, 840), (990, 1020)]
add_busy_constraints(solver, roy_busy)

# Brian is free the entire day; no busy intervals.

# Deborah's busy intervals:
# 12:00 to 13:00 --> [720, 780)
# 14:00 to 14:30 --> [840, 870)
# 15:30 to 16:00 --> [930, 960)
deborah_busy = [(720, 780), (840, 870), (930, 960)]
add_busy_constraints(solver, deborah_busy)

# Eric's busy intervals:
# 9:30 to 10:00  --> [570, 600)
# 11:30 to 12:00 --> [690, 720)
# 12:30 to 13:00 --> [750, 780)
# 14:00 to 16:00 --> [840, 960)
# 16:30 to 17:00 --> [990, 1020)
eric_busy = [(570, 600), (690, 720), (750, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, eric_busy)

# Susan's busy intervals:
# 9:00 to 10:00   --> [540, 600)
# 10:30 to 12:00  --> [630, 720)
# 12:30 to 14:30  --> [750, 870)
# 15:00 to 16:00  --> [900, 960)
# 16:30 to 17:00  --> [990, 1020)
susan_busy = [(540, 600), (630, 720), (750, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, susan_busy)

# Joyce's busy intervals:
# 9:30 to 10:00   --> [570, 600)
# 10:30 to 12:30  --> [630, 750)
# 14:00 to 15:00  --> [840, 900)
# 16:30 to 17:00  --> [990, 1020)
joyce_busy = [(570, 600), (630, 750), (840, 900), (990, 1020)]
add_busy_constraints(solver, joyce_busy)

# Iterate over possible start times to find a valid meeting slot.
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
from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either finish before busy_start, or start after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Alan's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
alan_busy = [(690, 720), (750, 780), (870, 900), (960, 990)]
add_busy_constraints(solver, alan_busy)

# Kyle has no meetings the whole day. (No constraints needed)

# Zachary's calendar is wide open. (No constraints needed)

# Heather has no meetings the whole day. (No constraints needed)

# Joan's busy intervals:
# 10:00 to 12:30 -> [600, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:30 -> [900, 990)
joan_busy = [(600, 750), (780, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, joan_busy)

# Diane's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:00 to 16:00 -> [720, 960)
diane_busy = [(600, 660), (720, 960)]
add_busy_constraints(solver, diane_busy)

# Julie's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 12:30 to 14:00  -> [750, 840)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 17:00  -> [930, 1020)
julie_busy = [(570, 660), (750, 840), (870, 900), (930, 1020)]
add_busy_constraints(solver, julie_busy)

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
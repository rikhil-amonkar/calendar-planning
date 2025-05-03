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

# Helper function to add constraints for busy intervals:
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration) 
# must either finish before busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Joshua's calendar is wide open, so no busy intervals.
# Alice's calendar is wide open, so no busy intervals.

# Gerald's busy intervals:
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
gerald_busy = [(870, 900), (930, 960)]
add_busy_constraints(solver, gerald_busy)

# Paul's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:30 -> [690, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
paul_busy = [(600, 630), (690, 750), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, paul_busy)

# Donald's busy intervals:
# 9:00 to 10:30 -> [540, 630)
# 12:30 to 14:00 -> [750, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
donald_busy = [(540, 630), (750, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, donald_busy)

# Richard's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 15:30 -> [780, 930)
# 16:30 to 17:00 -> [990, 1020)
richard_busy = [(540, 630), (660, 750), (780, 930), (990, 1020)]
add_busy_constraints(solver, richard_busy)

# Patrick's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 17:00 -> [900, 1020)
patrick_busy = [(570, 630), (690, 720), (780, 810), (900, 1020)]
add_busy_constraints(solver, patrick_busy)

# Iterate over possible start times to find a valid meeting time.
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
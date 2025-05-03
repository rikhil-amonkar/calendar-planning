from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints.
# For each busy interval (busy_start, busy_end), the meeting [start, start+duration)
# must either finish not later than busy_start, or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Alexander's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 17:00 -> [960, 1020)
alexander_busy = [(600, 630), (780, 840), (870, 900), (960, 1020)]
add_busy_constraints(solver, alexander_busy)

# Dylan's calendar is wide open: no busy intervals.

# Elizabeth's calendar is wide open: no busy intervals.

# Edward's busy intervals:
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 17:00 -> [690, 1020)
edward_busy = [(570, 660), (690, 1020)]
add_busy_constraints(solver, edward_busy)

# Douglas's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 15:30 -> [840, 930)
# 16:00 to 17:00 -> [960, 1020)
douglas_busy = [(600, 630), (660, 720), (750, 810), (840, 930), (960, 1020)]
add_busy_constraints(solver, douglas_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Latest possible start time is 1020 - duration = 990 minutes.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
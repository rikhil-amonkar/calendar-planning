from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint: Maria cannot meet before 9:30 (570 minutes).
solver.add(start >= 570)

# Helper function: For each busy interval (busy_start, busy_end),
# add constraints to ensure the meeting [start, start+duration) does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Maria's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 12:00  -> [660, 720)
# 15:30 to 16:00  -> [930, 960)
maria_busy = [(570, 600), (660, 720), (930, 960)]
add_busy_constraints(solver, maria_busy)

# Gary's busy intervals:
# 10:00 to 10:30  -> [600, 630)
# 13:00 to 13:30  -> [780, 810)
# 14:30 to 15:00  -> [870, 900)
# 16:30 to 17:00  -> [990, 1020)
gary_busy = [(600, 630), (780, 810), (870, 900), (990, 1020)]
add_busy_constraints(solver, gary_busy)

# Betty has no meetings, so no busy intervals for her.

# Charlotte's busy intervals:
# 9:30 to 12:00   -> [570, 720)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:00  -> [930, 960)
charlotte_busy = [(570, 720), (780, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, charlotte_busy)

# Jerry's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 12:30  -> [630, 750)
# 13:00 to 16:30  -> [780, 990)
jerry_busy = [(570, 600), (630, 750), (780, 990)]
add_busy_constraints(solver, jerry_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Latest valid start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
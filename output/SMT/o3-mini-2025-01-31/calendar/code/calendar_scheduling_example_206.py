from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Margaret's preference: do not meet before 14:30 (870 minutes).
solver.add(start >= 870)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either finish on or before busy_start, or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Shirley's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
shirley_busy = [(630, 660), (720, 750)]
add_busy_constraints(solver, shirley_busy)

# Jacob's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:00 -> [870, 900)
jacob_busy = [(540, 570), (600, 630), (660, 690), (750, 810), (870, 900)]
add_busy_constraints(solver, jacob_busy)

# Stephen's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
stephen_busy = [(690, 720), (750, 780)]
add_busy_constraints(solver, stephen_busy)

# Margaret's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:30 -> [630, 750)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
margaret_busy = [(540, 570), (630, 750), (780, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, margaret_busy)

# Mason's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
mason_busy = [(540, 600), (630, 660), (690, 750), (780, 810), (840, 870), (990, 1020)]
add_busy_constraints(solver, mason_busy)

# Search through all possible start times within the allowed range.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save current state before trying a candidate.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state before breaking out.
        break
    solver.pop()  # Restore state to try the next candidate.

if not solution_found:
    print("No valid meeting time could be found.")
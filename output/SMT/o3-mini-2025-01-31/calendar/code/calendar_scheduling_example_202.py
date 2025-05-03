from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints per busy interval.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start+duration)
# must end on or before busy_start or start on or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Lawrence is free all day: No constraints.

# Christine's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:30 to 13:00 -> [750, 780)
christine_busy = [(540, 570), (750, 780)]
add_busy_constraints(solver, christine_busy)

# Barbara's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
barbara_busy = [(630, 690), (720, 750), (780, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, barbara_busy)

# Stephanie's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
stephanie_busy = [(600, 660), (690, 720), (750, 810), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, stephanie_busy)

# Hannah's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00 -> [630, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 15:30 -> [840, 930)
# 16:00 to 16:30 -> [960, 990)
hannah_busy = [(540, 600), (630, 720), (750, 780), (840, 930), (960, 990)]
add_busy_constraints(solver, hannah_busy)

# Search for a valid meeting start time.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save state
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
        solver.pop()  # Restore state before exiting.
        break
    solver.pop()  # Restore state for next candidate

if not solution_found:
    print("No valid meeting time could be found.")
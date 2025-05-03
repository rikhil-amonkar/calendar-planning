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

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start+duration)
# must either finish before busy_start or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Elijah's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:00 to 12:30 -> [720, 750)
# 15:00 to 15:30 -> [900, 930)
elijah_busy = [(600, 660), (720, 750), (900, 930)]
add_busy_constraints(solver, elijah_busy)

# Janet's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 13:30 to 15:30 -> [810, 930)
janet_busy = [(570, 630), (810, 930)]
add_busy_constraints(solver, janet_busy)

# Brian is free the whole day: no constraints.

# Carl's busy intervals:
# 9:30 to 16:30 -> [570, 990)
carl_busy = [(570, 990)]
add_busy_constraints(solver, carl_busy)

# Timothy's busy intervals:
# 10:30 to 12:00 -> [630, 720)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:00 -> [870, 960)
# 16:30 to 17:00 -> [990, 1020)
timothy_busy = [(630, 720), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, timothy_busy)

# Search for a valid meeting start time.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save current state before setting a candidate start time.
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
        solver.pop()  # Restore solver state
        break
    solver.pop()  # Restore for the next candidate

if not solution_found:
    print("No valid meeting time could be found.")
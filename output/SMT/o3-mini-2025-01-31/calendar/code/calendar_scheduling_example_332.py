from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Constrain meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # To avoid overlapping with a busy interval [bs, be),
        # the meeting must finish on or before bs or start on/after be.
        s.add(Or(start + duration <= bs, start >= be))

# Pamela's busy intervals:
#   9:30 to 10:00 → [570, 600)
#   15:00 to 15:30 → [900, 930)
#   16:00 to 17:00 → [960, 1020)
pamela_busy = [(570, 600), (900, 930), (960, 1020)]
add_busy_constraints(solver, pamela_busy)

# Sandra is free the whole day: no constraints.

# Helen is free the whole day: no constraints.

# Zachary's busy intervals:
#   9:00 to 11:00 → [540, 660)
#   11:30 to 12:00 → [690, 720)
#   12:30 to 13:30 → [750, 810)
#   15:30 to 17:00 → [930, 1020)
zachary_busy = [(540, 660), (690, 720), (750, 810), (930, 1020)]
add_busy_constraints(solver, zachary_busy)

# Janice's busy intervals:
#   9:30 to 14:00 → [570, 840)
#   14:30 to 17:00 → [870, 1020)
janice_busy = [(570, 840), (870, 1020)]
add_busy_constraints(solver, janice_busy)

# Paul's busy intervals:
#   9:30 to 11:30 → [570, 690)
#   12:00 to 12:30 → [720, 750)
#   13:00 to 13:30 → [780, 810)
#   15:00 to 17:00 → [900, 1020)
paul_busy = [(570, 690), (720, 750), (780, 810), (900, 1020)]
add_busy_constraints(solver, paul_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")
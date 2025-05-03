from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Maria's personal preference: cannot meet before 12:30 (750 minutes)
solver.add(start >= 750)

# Helper function: For each busy interval [bs, be),
# add a constraint that the meeting [start, start+duration) does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Roger's busy intervals.
# 12:30 to 13:00 -> [750, 780)
# 16:30 to 17:00 -> [990, 1020)
roger_busy = [(750, 780), (990, 1020)]
add_busy_constraints(solver, roger_busy)

# Jesse's busy intervals.
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 14:30 -> [840, 870)
jesse_busy = [(600, 630), (750, 810), (840, 870)]
add_busy_constraints(solver, jesse_busy)

# Daniel's busy intervals.
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 13:30 -> [630, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
daniel_busy = [(540, 570), (630, 810), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, daniel_busy)

# Maria's busy intervals.
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 16:30 -> [900, 990)
maria_busy = [(540, 570), (600, 630), (660, 690), (720, 780), (810, 870), (900, 990)]
add_busy_constraints(solver, maria_busy)

# Try to find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state before breaking.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
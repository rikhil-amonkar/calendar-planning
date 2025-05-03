from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval [bs, be),
# ensure the meeting [start, start+duration) does not overlap with it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Kevin's busy intervals.
# 10:30 to 11:00 -> [630, 660)
# 14:00 to 14:30 -> [840, 870)
kevin_busy = [(630, 660), (840, 870)]
add_busy_constraints(solver, kevin_busy)

# Carolyn's busy intervals.
# 11:30 to 12:00 -> [690, 720)
# 16:00 to 16:30 -> [960, 990)
carolyn_busy = [(690, 720), (960, 990)]
add_busy_constraints(solver, carolyn_busy)

# Stephanie's busy intervals.
# 9:00 to 10:30 -> [540, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 17:00 -> [900, 1020)
stephanie_busy = [(540, 630), (660, 750), (810, 870), (900, 1020)]
add_busy_constraints(solver, stephanie_busy)

# Isabella's busy intervals.
# 9:00 to 9:30 -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 14:30 -> [690, 870)
# 15:00 to 17:00 -> [900, 1020)
isabella_busy = [(540, 570), (630, 660), (690, 870), (900, 1020)]
add_busy_constraints(solver, isabella_busy)

# Find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
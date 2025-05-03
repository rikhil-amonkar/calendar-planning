from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
# Meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)
# Alexander prefers not to meet before 13:00 (780 minutes)
solver.add(start >= 780)

# Helper function: For each busy interval [bs, be),
# the meeting interval [start, start+duration) should not overlap.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Danielle is free all day (no busy intervals).

# Janice's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 15:00 to 16:30 -> [900, 990)
janice_busy = [(540, 570), (900, 990)]
add_busy_constraints(solver, janice_busy)

# Alexander's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:30 -> [600, 750)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
alexander_busy = [(540, 570), (600, 750), (780, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, alexander_busy)

# Thomas' busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 13:00 to 13:30  -> [780, 810)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 16:30  -> [960, 990)
thomas_busy = [(540, 660), (780, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, thomas_busy)

# Try possible meeting start times starting from 780 (13:00) up to the last valid starting minute.
solution_found = False
for t in range(780, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
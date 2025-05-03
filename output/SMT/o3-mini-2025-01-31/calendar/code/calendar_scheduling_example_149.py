from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints so that the meeting does not overlap with any busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Diane is free all day (no busy intervals).

# Russell is free all day (no busy intervals).

# Kathryn's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 17:00  -> [870, 1020)
kathryn_busy = [(540, 600), (630, 690), (720, 780), (810, 840), (870, 1020)]
add_busy_constraints(solver, kathryn_busy)

# Joshua's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 11:30 to 12:30  -> [690, 750)
# 14:00 to 15:30  -> [840, 930)
# 16:00 to 17:00  -> [960, 1020)
joshua_busy = [(540, 570), (600, 660), (690, 750), (840, 930), (960, 1020)]
add_busy_constraints(solver, joshua_busy)

# Try to find a valid meeting time by iterating over possible starting times.
solution_found = False
for t in range(540, 1020 - duration + 1):
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
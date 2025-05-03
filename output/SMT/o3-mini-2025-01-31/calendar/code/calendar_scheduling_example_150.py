from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints so that the meeting [start, start+duration)
# does not overlap with any busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Andrew has no meetings all day.

# Dennis's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 12:00 to 12:30  -> [720, 750)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:00  -> [930, 960)
dennis_busy = [(570, 600), (720, 750), (840, 870), (930, 960)]
add_busy_constraints(solver, dennis_busy)

# Nancy's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:30  -> [690, 750)
# 14:00 to 15:00  -> [840, 900)
# 16:00 to 16:30  -> [960, 990)
nancy_busy = [(570, 660), (690, 750), (840, 900), (960, 990)]
add_busy_constraints(solver, nancy_busy)

# Alexander's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 12:30  -> [720, 750)
# 14:00 to 15:30  -> [840, 930)
# 16:30 to 17:00  -> [990, 1020)
alexander_busy = [(540, 570), (630, 690), (720, 750), (840, 930), (990, 1020)]
add_busy_constraints(solver, alexander_busy)

# Try possible start times from 9:00 (540 minutes) to latest valid (990 minutes)
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
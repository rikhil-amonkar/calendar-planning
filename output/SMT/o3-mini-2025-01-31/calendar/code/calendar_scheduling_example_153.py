from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints so that the meeting [start, start+duration)
# does not overlap any busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Logan's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 16:30 to 17:00 -> [990, 1020)
logan_busy = [(660, 690), (990, 1020)]
add_busy_constraints(solver, logan_busy)

# Bruce's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
bruce_busy = [(540, 570), (600, 630), (840, 870), (900, 930)]
add_busy_constraints(solver, bruce_busy)

# Joan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 12:30 to 14:00 -> [750, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
joan_busy = [(540, 570), (600, 660), (750, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, joan_busy)

# Kevin's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 11:30 to 13:30  -> [690, 810)
# 14:30 to 17:00  -> [870, 1020)
kevin_busy = [(540, 570), (690, 810), (870, 1020)]
add_busy_constraints(solver, kevin_busy)

# Try to find a valid meeting time by checking possible start times.
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
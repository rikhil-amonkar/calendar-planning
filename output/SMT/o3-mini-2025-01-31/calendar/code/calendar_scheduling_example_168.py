from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval [bs, be), the meeting interval [start, start+duration)
# must either finish before the busy interval starts, or start after it ends.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jean's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 17:00 -> [960, 1020)
jean_busy = [(780, 810), (840, 870), (960, 1020)]
add_busy_constraints(solver, jean_busy)

# Lauren's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
lauren_busy = [(570, 600), (630, 660)]
add_busy_constraints(solver, lauren_busy)

# Olivia's busy intervals:
# 9:00 to 11:00  -> [540, 660)
# 12:30 to 16:00 -> [750, 960)
# 16:30 to 17:00 -> [990, 1020)
olivia_busy = [(540, 660), (750, 960), (990, 1020)]
add_busy_constraints(solver, olivia_busy)

# Scott's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:30  -> [870, 930)
scott_busy = [(540, 690), (810, 840), (870, 930)]
add_busy_constraints(solver, scott_busy)

# Search for the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
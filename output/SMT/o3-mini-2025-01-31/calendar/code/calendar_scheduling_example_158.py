from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Add Philip's preference to avoid meetings before 13:30.
# 13:30 in minutes is 810.
solver.add(start >= 810)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before bs starts or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Russell's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 13:00 to 13:30 -> [780, 810)
# 15:30 to 16:30 -> [930, 990)
russell_busy = [(570, 600), (780, 810), (930, 990)]
add_busy_constraints(solver, russell_busy)

# Debra's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
debra_busy = [(660, 690), (780, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, debra_busy)

# Philip's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:30 -> [630, 750)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 17:00 -> [930, 1020)
philip_busy = [(540, 570), (630, 750), (840, 900), (930, 1020)]
add_busy_constraints(solver, philip_busy)

# Peter's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 15:00 -> [780, 900)
# 15:30 to 16:00 -> [930, 960)
peter_busy = [(540, 570), (600, 690), (720, 750), (780, 900), (930, 960)]
add_busy_constraints(solver, peter_busy)

# Since Philip prefers not to have meetings before 13:30, the earliest possible start is 810.
# We iterate from 810 to the maximum available start time.
solution_found = False
for t in range(810, 1020 - duration + 1):
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
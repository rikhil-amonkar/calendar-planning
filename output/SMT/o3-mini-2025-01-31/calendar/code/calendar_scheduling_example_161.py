from z3 import *

# Create the Z3 solver
solver = Solver()

# Meeting parameters: work hours from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Margaret would rather not meet on Monday before 13:30 (810 minutes)
solver.add(start >= 810)

# Helper function to add busy constraints:
# For each busy interval [bs, be), the meeting must either finish before bs or start on/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Ryan's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:00 -> [930, 960)
ryan_busy = [(750, 780), (930, 960)]
add_busy_constraints(solver, ryan_busy)

# Margaret's busy intervals:
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
margaret_busy = [(660, 720), (780, 810), (840, 870)]
add_busy_constraints(solver, margaret_busy)

# Willie's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 15:30  -> [810, 930)
# 16:30 to 17:00  -> [990, 1020)
willie_busy = [(570, 660), (720, 780), (810, 930), (990, 1020)]
add_busy_constraints(solver, willie_busy)

# Shirley's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
shirley_busy = [(600, 630), (660, 690), (720, 780), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, shirley_busy)

# Try to find a valid meeting start time by checking potential start times.
solution_found = False
# We iterate from the earliest possible start (max(540, Margaret's preference)) to latest possible start.
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
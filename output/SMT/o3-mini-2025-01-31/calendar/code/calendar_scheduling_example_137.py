from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Diana cannot meet before 14:00 (840 minutes), so we use that as our lower bound.
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 840, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Rebecca's busy intervals:
# 10:30 to 11:00 -> [630, 660]
# 12:30 to 13:00 -> [750, 780]
rebecca_busy = [(630, 660), (750, 780)]
add_busy_constraints(solver, rebecca_busy)

# Donald's busy intervals:
# 12:00 to 12:30 -> [720, 750]
# 15:00 to 15:30 -> [900, 930]
donald_busy = [(720, 750), (900, 930)]
add_busy_constraints(solver, donald_busy)

# Diana's busy intervals:
# 9:30 to 11:00   -> [570, 660]
# 12:30 to 13:00  -> [750, 780]
# 13:30 to 14:00  -> [810, 840]
# 14:30 to 17:00  -> [870, 1020]
diana_busy = [(570, 660), (750, 780), (810, 840), (870, 1020)]
add_busy_constraints(solver, diana_busy)
# Note: Additionally, Diana cannot meet before 14:00, which is already enforced by start >= 840.

# Jesse's busy intervals:
# 9:30 to 12:30 -> [570, 750]
# 13:00 to 13:30 -> [780, 810]
# 14:30 to 15:00 -> [870, 900]
# 16:00 to 17:00 -> [960, 1020]
jesse_busy = [(570, 750), (780, 810), (870, 900), (960, 1020)]
add_busy_constraints(solver, jesse_busy)

# Find a valid meeting time by scanning through possible start times.
solution_found = False
for t in range(840, 1020 - duration + 1):
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
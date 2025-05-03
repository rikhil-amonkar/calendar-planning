from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so start must satisfy:
#     start >= 540  and  start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must finish on or before bs,
    # or start at or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Eric has no meetings, so no busy constraints are needed for him.

# Ashley's busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 12:00 -> [660, 720]
# 12:30 to 13:00 -> [750, 780]
# 15:00 to 16:00 -> [900, 960]
ashley_busy = [(600, 630), (660, 720), (750, 780), (900, 960)]
add_busy_constraints(solver, ashley_busy)

# Ronald's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 11:30 -> [600, 690]
# 12:30 to 14:00 -> [750, 840]
# 14:30 to 17:00 -> [870, 1020]
ronald_busy = [(540, 570), (600, 690), (750, 840), (870, 1020)]
add_busy_constraints(solver, ronald_busy)

# Larry's busy intervals:
# 9:00 to 12:00  -> [540, 720]
# 13:00 to 17:00 -> [780, 1020]
larry_busy = [(540, 720), (780, 1020)]
add_busy_constraints(solver, larry_busy)

# Find a valid meeting time by scanning possible times (e.g., the earliest possible).
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
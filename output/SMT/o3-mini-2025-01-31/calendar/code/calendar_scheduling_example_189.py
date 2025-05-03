from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes
duration = 30
start = Int("start")

# Ensure the meeting stays within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting interval
# [start, start+duration) must not overlap: it must finish by busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Judy's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 15:00 to 15:30 -> [900, 930)
judy_busy = [(570, 600), (900, 930)]
add_busy_constraints(solver, judy_busy)

# Lori's busy intervals:
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
lori_busy = [(870, 900), (960, 990)]
add_busy_constraints(solver, lori_busy)

# Andrea's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
andrea_busy = [(540, 570), (630, 690), (750, 780), (810, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, andrea_busy)

# Mark's busy intervals:
# 9:30 to 14:00  -> [570, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 17:00 -> [960, 1020)
mark_busy = [(570, 840), (870, 900), (960, 1020)]
add_busy_constraints(solver, mark_busy)

# Search for a valid start time.
solution_found = False
# The meeting start time can be from 540 to (1020 - duration) = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
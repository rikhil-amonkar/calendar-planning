from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Lauren cannot meet after 14:30 (870 minutes), 
# so the meeting must finish by 14:30.
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must start no earlier than 9:00 and finish by 14:30 (Lauren's constraint).
solver.add(start >= 540, start + duration <= 870)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting should either finish before a busy interval starts 
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Alexander is free all day: no constraints.

# Lauren's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 14:30 to 15:00 -> [870, 900)
lauren_busy = [(570, 600), (870, 900)]
add_busy_constraints(solver, lauren_busy)

# Arthur is free all day: no constraints.

# Willie's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 12:30 to 14:00 -> [750, 840)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
willie_busy = [(570, 690), (750, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, willie_busy)

# Lori's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 13:30  -> [720, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:00  -> [900, 960)
lori_busy = [(570, 600), (660, 690), (720, 810), (840, 870), (900, 960)]
add_busy_constraints(solver, lori_busy)

# Search for the earliest valid meeting time.
solution_found = False
# With the Lauren constraint, the latest valid start is 870 - duration = 840.
for t in range(540, 841):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
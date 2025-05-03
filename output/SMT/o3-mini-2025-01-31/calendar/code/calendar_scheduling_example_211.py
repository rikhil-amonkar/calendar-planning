from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval [busy_start, busy_end),
# the meeting [start, start+duration) must be scheduled so that it does not overlap with it.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Douglas: free the whole day, so no constraints.

# Mary is busy:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
mary_busy = [(570, 600), (660, 690)]
add_busy_constraints(solver, mary_busy)

# Billy is busy:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 13:30 to 14:30  -> [810, 870)
billy_busy = [(540, 600), (630, 690), (810, 870)]
add_busy_constraints(solver, billy_busy)

# Russell is busy:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 11:30  -> [660, 690)
# 13:30 to 16:00  -> [810, 960)
# 16:30 to 17:00  -> [990, 1020)
russell_busy = [(570, 600), (660, 690), (810, 960), (990, 1020)]
add_busy_constraints(solver, russell_busy)

# Judy is busy:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 17:00  -> [750, 1020)
judy_busy = [(540, 600), (630, 720), (750, 1020)]
add_busy_constraints(solver, judy_busy)

# Iterate over possible start times to find the earliest valid meeting time.
solution_found = False
# The meeting must start between 9:00 (540) and 16:30 (990) because meeting ends by 1020.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before the busy interval starts or start at/after it ends.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Alexander's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
alex_busy = [(540, 570), (660, 690), (930, 960), (990, 1020)]
add_busy_constraints(solver, alex_busy)

# Paul's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:30 to 13:00 -> [750, 780)
paul_busy = [(540, 570), (750, 780)]
add_busy_constraints(solver, paul_busy)

# Elijah's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 17:00 -> [720, 1020)
elijah_busy = [(570, 600), (660, 690), (720, 1020)]
add_busy_constraints(solver, elijah_busy)

# Mark's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 13:30  -> [720, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
mark_busy = [(540, 600), (630, 690), (720, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, mark_busy)

# We seek the earliest available meeting time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")
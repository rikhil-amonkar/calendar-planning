from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes. Thus, start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting [start, start+duration)
# does not overlap with a given busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Janice's busy intervals:
# 11:30 to 12:30 -> [690, 750]
janice_busy = [(690, 750)]
add_busy_constraints(solver, janice_busy)

# Isabella has no meetings, so no busy constraints are added.

# Linda's busy intervals:
# 9:30 to 11:30    -> [570, 690]
# 12:00 to 13:00   -> [720, 780]
# 13:30 to 16:30   -> [810, 990]
linda_busy = [(570, 690), (720, 780), (810, 990)]
add_busy_constraints(solver, linda_busy)

# Billy's busy intervals:
# 9:00 to 9:30     -> [540, 570]
# 10:30 to 11:30   -> [630, 690]
# 13:30 to 14:00   -> [810, 840]
# 14:30 to 16:00   -> [870, 960]
# 16:30 to 17:00   -> [990, 1020]
billy_busy = [(540, 570), (630, 690), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, billy_busy)

# Check for a valid meeting time that satisfies all constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
        start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")
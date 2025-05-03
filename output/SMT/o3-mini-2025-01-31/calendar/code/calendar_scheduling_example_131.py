from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes
duration = 60
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must either finish by bs or start at/after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Walter's busy intervals:
# 9:30 to 10:00 -> [570, 600]
# 13:00 to 13:30 -> [780, 810]
walter_busy = [(570, 600), (780, 810)]
add_busy_constraints(solver, walter_busy)

# Jacob's busy intervals:
# 11:00 to 11:30 -> [660, 690]
# 13:00 to 13:30 -> [780, 810]
jacob_busy = [(660, 690), (780, 810)]
add_busy_constraints(solver, jacob_busy)

# Jennifer's busy intervals:
# 9:30 to 10:30  -> [570, 630]
# 11:30 to 12:00 -> [690, 720]
# 12:30 to 15:00 -> [750, 900]
jennifer_busy = [(570, 630), (690, 720), (750, 900)]
add_busy_constraints(solver, jennifer_busy)

# Joan's busy intervals:
# 9:30 to 10:00  -> [570, 600]
# 10:30 to 11:30 -> [630, 690]
# 12:00 to 12:30 -> [720, 750]
# 13:00 to 14:00 -> [780, 840]
# 14:30 to 15:30 -> [870, 930]
joan_busy = [(570, 600), (630, 690), (720, 750), (780, 840), (870, 930)]
add_busy_constraints(solver, joan_busy)

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
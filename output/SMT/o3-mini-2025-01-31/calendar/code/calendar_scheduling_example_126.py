from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so start must satisfy:
# start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Lawrence would rather not meet before 13:00 (780 minutes).
solver.add(start >= 780)

# Helper function to ensure that the meeting (start, start+duration)
# does not overlap with a given busy interval [bs, be).
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Lawrence's busy intervals:
# 14:00 to 16:00 -> [840, 960]
lawrence_busy = [(840, 960)]
add_busy_constraints(lawrence_busy)

# Sharon's busy intervals:
# 10:30 to 11:00 -> [630, 660]
# 12:30 to 13:30 -> [750, 810]
# 15:00 to 15:30 -> [900, 930]
sharon_busy = [(630, 660), (750, 810), (900, 930)]
add_busy_constraints(sharon_busy)

# Aaron's busy intervals:
# 9:30 to 11:30   -> [570, 690]
# 12:00 to 14:00  -> [720, 840]
# 14:30 to 16:00  -> [870, 960]
# 16:30 to 17:00  -> [990, 1020]
aaron_busy = [(570, 690), (720, 840), (870, 960), (990, 1020)]
add_busy_constraints(aaron_busy)

# Amy's busy intervals:
# 9:30 to 11:00   -> [570, 660]
# 12:00 to 13:00  -> [720, 780]
# 14:00 to 16:00  -> [840, 960]
# 16:30 to 17:00  -> [990, 1020]
amy_busy = [(570, 660), (720, 780), (840, 960), (990, 1020)]
add_busy_constraints(amy_busy)

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
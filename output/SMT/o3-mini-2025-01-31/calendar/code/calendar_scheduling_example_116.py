from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable (in minutes from midnight).
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration: 30 minutes, so start must satisfy start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Anna prefers not to meet before 14:30. 14:30 is 14*60 + 30 = 870 minutes.
solver.add(start >= 870)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval (bs, be), the meeting (start, start+duration)
# must either finish by or before bs or begin at or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Adam's busy intervals:
# 14:00 to 15:00 -> [840, 900]
adam_busy = [(840, 900)]
add_busy_constraints(adam_busy)

# John's busy intervals:
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 14:30 -> [840, 870]
# 15:30 to 16:00 -> [930, 960]
# 16:30 to 17:00 -> [990, 1020]
john_busy = [(780, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(john_busy)

# Stephanie's busy intervals:
# 9:30 to 10:00   -> [570, 600]
# 10:30 to 11:00  -> [630, 660]
# 11:30 to 16:00  -> [690, 960]
# 16:30 to 17:00  -> [990, 1020]
stephanie_busy = [(570, 600), (630, 660), (690, 960), (990, 1020)]
add_busy_constraints(stephanie_busy)

# Anna's busy intervals:
# 9:30 to 10:00   -> [570, 600]
# 12:00 to 12:30  -> [720, 750]
# 13:00 to 15:30  -> [780, 930]
# 16:30 to 17:00  -> [990, 1020]
anna_busy = [(570, 600), (720, 750), (780, 930), (990, 1020)]
add_busy_constraints(anna_busy)

# Check for a valid meeting time and print the solution in HH:MM format.
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
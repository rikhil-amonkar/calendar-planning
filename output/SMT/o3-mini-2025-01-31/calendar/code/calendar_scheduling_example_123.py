from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so: start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: ensure the meeting (start, start + duration)
# does not overlap with any given busy interval (bs, be).
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Thomas has no meetings, so no busy intervals.

# Catherine's busy intervals:
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 15:30 -> [840, 930]
catherine_busy = [(780, 810), (840, 930)]
add_busy_constraints(catherine_busy)

# Ruth's busy intervals:
# 9:30 to 14:30 -> [570, 870]
# 15:30 to 16:30 -> [930, 990]
ruth_busy = [(570, 870), (930, 990)]
add_busy_constraints(ruth_busy)

# Andrew's busy intervals:
# 9:00 to 10:00  -> [540, 600]
# 10:30 to 12:00 -> [630, 720]
# 12:30 to 13:00 -> [750, 780]
# 14:00 to 14:30 -> [840, 870]
# 15:30 to 16:00 -> [930, 960]
andrew_busy = [(540, 600), (630, 720), (750, 780), (840, 870), (930, 960)]
add_busy_constraints(andrew_busy)

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
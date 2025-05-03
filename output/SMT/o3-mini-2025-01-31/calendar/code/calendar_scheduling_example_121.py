from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so: start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval (bs, be), the meeting (start, start+duration)
# must either finish by bs or start at or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jerry's busy intervals:
# 11:30 to 12:00 -> [690, 720]
# 16:00 to 16:30 -> [960, 990]
jerry_busy = [(690, 720), (960, 990)]
add_busy_constraints(jerry_busy)

# Benjamin's busy intervals: none (calendar is wide open)

# Andrew's busy intervals:
# 9:30 to 10:30  -> [570, 630]
# 11:30 to 12:30 -> [690, 750]
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 15:30 -> [840, 930]
andrew_busy = [(570, 630), (690, 750), (780, 810), (840, 930)]
add_busy_constraints(andrew_busy)

# Anna's busy intervals:
# 9:00 to 11:30  -> [540, 690]
# 12:00 to 12:30 -> [720, 750]
# 13:00 to 17:00 -> [780, 1020]
anna_busy = [(540, 690), (720, 750), (780, 1020)]
add_busy_constraints(anna_busy)

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
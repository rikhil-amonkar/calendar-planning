from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540) to 17:00 (1020)
# Meeting duration: 30 minutes, so start must satisfy start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval (bs, be), the meeting (start, start+duration)
# must either end on or before bs, or start on or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Ruth's busy intervals:
# 9:30 to 10:00   -> [570, 600]
# 11:00 to 11:30  -> [660, 690]
# 12:00 to 12:30  -> [720, 750]
# 13:00 to 13:30  -> [780, 810]
# 14:30 to 15:00  -> [870, 900]
# 16:00 to 16:30  -> [960, 990]
ruth_busy = [(570, 600), (660, 690), (720, 750), (780, 810), (870, 900), (960, 990)]
add_busy_constraints(ruth_busy)

# Angela's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 12:30 to 13:00  -> [750, 780]
# 13:30 to 15:00  -> [810, 900]
# 16:00 to 16:30  -> [960, 990]
angela_busy = [(540, 570), (750, 780), (810, 900), (960, 990)]
add_busy_constraints(angela_busy)

# Lisa's busy intervals:
# 10:30 to 11:00  -> [630, 660]
# 11:30 to 14:00  -> [690, 840]
# 14:30 to 15:30  -> [870, 930]
# 16:00 to 17:00  -> [960, 1020]
lisa_busy = [(630, 660), (690, 840), (870, 930), (960, 1020)]
add_busy_constraints(lisa_busy)

# Cheryl's busy intervals:
# 9:00 to 10:30   -> [540, 630]
# 11:00 to 11:30  -> [660, 690]
# 12:30 to 14:00  -> [750, 840]
# 16:00 to 16:30  -> [960, 990]
cheryl_busy = [(540, 630), (660, 690), (750, 840), (960, 990)]
add_busy_constraints(cheryl_busy)

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
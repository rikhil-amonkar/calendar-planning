from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration is 30 minutes, so start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Jesse prefers not to have a meeting before 12:30 (750 minutes).
solver.add(start >= 750)

# Helper function to impose that the meeting (start, start+duration)
# does not overlap with each busy interval.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jesse's busy intervals:
# 12:30 to 13:00 -> [750, 780]
# 15:00 to 15:30 -> [900, 930]
jesse_busy = [(750, 780), (900, 930)]
add_busy_constraints(jesse_busy)

# Alan's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 16:00 to 16:30 -> [960, 990]
alan_busy = [(540, 570), (960, 990)]
add_busy_constraints(alan_busy)

# Elijah's busy intervals:
# 9:00 to 12:00   -> [540, 720]
# 12:30 to 13:00  -> [750, 780]
# 14:00 to 15:00  -> [840, 900]
# 15:30 to 17:00  -> [930, 1020]
elijah_busy = [(540, 720), (750, 780), (840, 900), (930, 1020)]
add_busy_constraints(elijah_busy)

# Amy's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 12:00 -> [630, 720]
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 15:00 -> [840, 900]
# 16:00 to 16:30 -> [960, 990]
amy_busy = [(540, 570), (630, 720), (780, 810), (840, 900), (960, 990)]
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
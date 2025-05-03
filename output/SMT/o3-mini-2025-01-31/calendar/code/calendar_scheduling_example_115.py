from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so start must satisfy start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Add Catherine's preference: she would rather not meet before 14:00 (840 minutes).
solver.add(start >= 840)

# Helper function to add constraints for busy intervals.
# For each busy interval (bs, be), the meeting (start, start + duration),
# must either finish on or before bs, or start on or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jose has no meetings, so we don't add any constraints for him.

# Catherine's busy intervals:
# 12:00 to 12:30 --> [720, 750]
# 15:00 to 15:30 --> [900, 930]
catherine_busy = [(720, 750), (900, 930)]
add_busy_constraints(catherine_busy)

# Rachel's busy intervals:
# 9:00 to 9:30   --> [540, 570]
# 10:00 to 11:00 --> [600, 660]
# 11:30 to 12:00 --> [690, 720]
# 12:30 to 13:00 --> [750, 780]
# 14:00 to 16:00 --> [840, 960]
# 16:30 to 17:00 --> [990, 1020]
rachel_busy = [(540, 570), (600, 660), (690, 720), (750, 780), (840, 960), (990, 1020)]
add_busy_constraints(rachel_busy)

# Lori's busy intervals:
# 9:00 to 12:00   --> [540, 720]
# 13:00 to 13:30  --> [780, 810]
# 14:30 to 15:30  --> [870, 930]
# 16:30 to 17:00  --> [990, 1020]
lori_busy = [(540, 720), (780, 810), (870, 930), (990, 1020)]
add_busy_constraints(lori_busy)

# Try to solve the constraints and print out a valid meeting time in HH:MM format.
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
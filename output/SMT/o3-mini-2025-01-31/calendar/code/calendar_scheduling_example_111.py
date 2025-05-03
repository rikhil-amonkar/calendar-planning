from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so meeting must start between 540 and 1020 - 30 = 990.
start = Int('start')
solver.add(start >= 540, start + 30 <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either end at or before bs, or start at or after be.
        solver.add(Or(start + 30 <= bs, start >= be))

# Gregory's busy intervals:
# 9:00 to 10:00   -> [540, 600]
# 10:30 to 11:30  -> [630, 690]
# 12:30 to 13:00  -> [750, 780]
# 13:30 to 14:00  -> [810, 840]
gregory_busy = [(540, 600), (630, 690), (750, 780), (810, 840)]
add_busy_constraints(gregory_busy)

# Natalie has a completely open calendar, so no constraints are added for her.

# Christine's busy intervals:
# 9:00 to 11:30  -> [540, 690]
# 13:30 to 17:00 -> [810, 1020]
christine_busy = [(540, 690), (810, 1020)]
add_busy_constraints(christine_busy)

# Vincent's busy intervals:
# 9:00 to 9:30    -> [540, 570]
# 10:30 to 12:00  -> [630, 720]
# 12:30 to 14:00  -> [750, 840]
# 14:30 to 17:00  -> [870, 1020]
vincent_busy = [(540, 570), (630, 720), (750, 840), (870, 1020)]
add_busy_constraints(vincent_busy)

# Check for a valid meeting time and print the solution in HH:MM format.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + 30
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
        start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")
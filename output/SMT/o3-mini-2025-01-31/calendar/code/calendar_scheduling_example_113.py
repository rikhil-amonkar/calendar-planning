from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable, measured in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration: 30 minutes, so we require: start >= 540 and start + 30 <= 1020.
start = Int('start')
solver.add(start >= 540, start + 30 <= 1020)

# Helper function to add constraints preventing the meeting from overlapping busy intervals.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish at or before bs, or start at or after be.
        solver.add(Or(start + 30 <= bs, start >= be))

# Bradley's busy intervals:
# - 9:30 to 10:00   -> [570, 600]
# - 12:30 to 13:00  -> [750, 780]
# - 13:30 to 14:00  -> [810, 840]
# - 15:30 to 16:00  -> [930, 960]
bradley_busy = [(570, 600), (750, 780), (810, 840), (930, 960)]
add_busy_constraints(bradley_busy)

# Teresa's busy intervals:
# - 10:30 to 11:00  -> [630, 660]
# - 12:00 to 12:30  -> [720, 750]
# - 13:00 to 13:30  -> [780, 810]
# - 14:30 to 15:00  -> [870, 900]
teresa_busy = [(630, 660), (720, 750), (780, 810), (870, 900)]
add_busy_constraints(teresa_busy)

# Elizabeth's busy intervals:
# - 9:00 to 9:30   -> [540, 570]
# - 10:30 to 11:30 -> [630, 690]
# - 13:00 to 13:30 -> [780, 810]
# - 14:30 to 15:00 -> [870, 900]
# - 15:30 to 17:00 -> [930, 1020]
elizabeth_busy = [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)]
add_busy_constraints(elizabeth_busy)

# Christian's busy intervals:
# - 9:00 to 9:30   -> [540, 570]
# - 10:30 to 17:00 -> [630, 1020]
christian_busy = [(540, 570), (630, 1020)]
add_busy_constraints(christian_busy)

# Check for a valid meeting slot that satisfies all constraints.
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
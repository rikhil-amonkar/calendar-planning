from z3 import *

# Create the Z3 solver instance
solver = Solver()

# Define the meeting start time variable (in minutes since midnight)
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so start must satisfy: start >= 540 and start + 30 <= 1020.
start = Int('start')
solver.add(start >= 540, start + 30 <= 1020)

# Helper function: for each busy interval (busy_start, busy_end), the meeting (start, start+30)
# must not overlap; thus, meeting ends on or before busy_start or starts on or after busy_end.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + 30 <= busy_start, start >= busy_end))

# Jean's busy intervals:
# 11:00 to 11:30 -> [660, 690]
# 12:30 to 13:30 -> [750, 810]
# 14:00 to 14:30 -> [840, 870]
# 15:00 to 15:30 -> [900, 930]
# 16:30 to 17:00 -> [990, 1020]
jean_busy = [(660, 690), (750, 810), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(jean_busy)

# Jose has no meetings, so no constraints are added for Jose.

# Samuel's busy intervals:
# 9:00 to 12:00 -> [540, 720]
# 12:30 to 16:00 -> [750, 960]
# 16:30 to 17:00 -> [990, 1020]
samuel_busy = [(540, 720), (750, 960), (990, 1020)]
add_busy_constraints(samuel_busy)

# Henry's busy intervals:
# 9:00 to 10:30 -> [540, 630]
# 14:00 to 14:30 -> [840, 870]
# 15:00 to 17:00 -> [900, 1020]
henry_busy = [(540, 630), (840, 870), (900, 1020)]
add_busy_constraints(henry_busy)

# Now, check if the constraints are satisfiable and extract the meeting time.
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
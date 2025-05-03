from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable, in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration: 60 minutes, so meeting must start such that start + 60 <= 1020.
start = Int('start')
solver.add(start >= 540, start + 60 <= 1020)

# Helper function to add constraints ensuring the meeting does not overlap a busy interval.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        # The meeting (start, start+60) must either finish at or before bs,
        # or start at or after be.
        solver.add(Or(start + 60 <= bs, start >= be))

# Stephanie's busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 16:00 to 16:30 -> [960, 990]
stephanie_busy = [(600, 630), (960, 990)]
add_busy_constraints(stephanie_busy)

# Cheryl's busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 11:30 to 12:00 -> [690, 720]
# 13:30 to 14:00 -> [810, 840]
# 16:30 to 17:00 -> [990, 1020]
cheryl_busy = [(600, 630), (690, 720), (810, 840), (990, 1020)]
add_busy_constraints(cheryl_busy)

# Bradley's busy intervals:
# 9:30 to 10:00   -> [570, 600]
# 10:30 to 11:30  -> [630, 690]
# 13:30 to 14:00  -> [810, 840]
# 14:30 to 15:00  -> [870, 900]
# 15:30 to 17:00  -> [930, 1020]
bradley_busy = [(570, 600), (630, 690), (810, 840), (870, 900), (930, 1020)]
add_busy_constraints(bradley_busy)

# Steven's busy intervals:
# 9:00 to 12:00   -> [540, 720]
# 13:00 to 13:30  -> [780, 810]
# 14:30 to 17:00  -> [870, 1020]
steven_busy = [(540, 720), (780, 810), (870, 1020)]
add_busy_constraints(steven_busy)

# Check for a valid meeting time that satisfies all constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + 60
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
        start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")
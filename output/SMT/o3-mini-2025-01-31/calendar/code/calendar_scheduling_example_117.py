from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 is 540 minutes to 17:00 is 1020 minutes.
# Meeting duration: 30 minutes, so meeting must satisfy start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Jesse's preference: avoid meetings on Monday after 15:00.
# That means the meeting must finish at or before 15:00 (15:00 is 900 minutes).
solver.add(start + duration <= 900)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval (bs, be), the meeting (start, start+duration) must either end by bs 
# or start at or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Brian's busy intervals:
# 9:00 to 9:30 -> [540, 570]
# 12:00 to 13:00 -> [720, 780]
# 14:00 to 14:30 -> [840, 870]
brian_busy = [(540, 570), (720, 780), (840, 870)]
add_busy_constraints(brian_busy)

# Ronald's busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 11:30 to 12:00 -> [690, 720]
# 14:00 to 14:30 -> [840, 870]
# 16:30 to 17:00 -> [990, 1020]
ronald_busy = [(600, 630), (690, 720), (840, 870), (990, 1020)]
add_busy_constraints(ronald_busy)

# Denise's busy intervals:
# 9:30 to 10:00 -> [570, 600]
# 11:00 to 12:30 -> [660, 750]
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 15:00 -> [840, 900]
# 15:30 to 17:00 -> [930, 1020]
denise_busy = [(570, 600), (660, 750), (780, 810), (840, 900), (930, 1020)]
add_busy_constraints(denise_busy)

# Jesse's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 11:00 -> [630, 660]
# 11:30 to 12:00 -> [690, 720]
# 12:30 to 13:30 -> [750, 810]
# 14:00 to 15:00 -> [840, 900]
# 15:30 to 16:00 -> [930, 960]
jesse_busy = [(540, 570), (630, 660), (690, 720), (750, 810), (840, 900), (930, 960)]
add_busy_constraints(jesse_busy)

# Check if there is a valid meeting time that satisfies all constraints.
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
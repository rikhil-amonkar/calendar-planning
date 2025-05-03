from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
# Additionally, Christopher prefers no meetings after 13:00, so the meeting must end by 13:00 (780 minutes).
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Christopher's preference: meeting must end by 13:00 (780 minutes)
solver.add(start + duration <= 780)

# Helper function to add busy interval constraints.
# For each busy interval (bs, be), the meeting (start, start+duration)
# should either end by bs or start at or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Debra's busy intervals:
# 9:00 to 10:00  -> [540, 600]
# 12:00 to 12:30 -> [720, 750]
# 13:00 to 14:30 -> [780, 870]
debra_busy = [(540, 600), (720, 750), (780, 870)]
add_busy_constraints(debra_busy)

# Christopher's busy intervals:
# 9:30 to 10:00  -> [570, 600]
# 12:00 to 13:00 -> [720, 780]
# 13:30 to 14:00 -> [810, 840]
# 14:30 to 15:00 -> [870, 900]
# 16:30 to 17:00 -> [990, 1020]
christopher_busy = [(570, 600), (720, 780), (810, 840), (870, 900), (990, 1020)]
add_busy_constraints(christopher_busy)

# Evelyn's busy intervals:
# 9:30 to 10:30  -> [570, 630]
# 11:30 to 12:00 -> [690, 720]
# 12:30 to 14:30 -> [750, 870]
# 15:30 to 16:00 -> [930, 960]
evelyn_busy = [(570, 630), (690, 720), (750, 870), (930, 960)]
add_busy_constraints(evelyn_busy)

# Wayne's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 12:30 -> [660, 750]
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 16:00 -> [840, 960]
wayne_busy = [(540, 570), (600, 630), (660, 750), (780, 810), (840, 960)]
add_busy_constraints(wayne_busy)

# Check for a valid meeting time that satisfies all constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")
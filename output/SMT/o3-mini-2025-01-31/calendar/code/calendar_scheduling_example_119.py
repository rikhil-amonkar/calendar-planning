from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so we require start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints with busy intervals.
# For each busy interval (bs, be), the meeting (start, start+duration)
# must either end on or before bs, or start on or after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Scott's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 11:30 -> [630, 690]
# 13:30 to 14:00 -> [810, 840]
# 14:30 to 15:30 -> [870, 930]
scott_busy = [(540, 570), (630, 690), (810, 840), (870, 930)]
add_busy_constraints(scott_busy)

# Laura's busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 14:30 to 15:00 -> [870, 900]
laura_busy = [(600, 630), (870, 900)]
add_busy_constraints(laura_busy)

# Marilyn's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 15:00 -> [600, 900]
# 15:30 to 17:00 -> [930, 1020]
marilyn_busy = [(540, 570), (600, 900), (930, 1020)]
add_busy_constraints(marilyn_busy)

# Natalie's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 12:00 -> [660, 720]
# 12:30 to 16:00 -> [750, 960]
# 16:30 to 17:00 -> [990, 1020]
natalie_busy = [(540, 570), (600, 630), (660, 720), (750, 960), (990, 1020)]
add_busy_constraints(natalie_busy)

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
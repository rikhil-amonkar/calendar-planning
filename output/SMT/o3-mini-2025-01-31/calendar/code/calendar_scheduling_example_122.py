from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define the meeting start time variable in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so we require start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For a given busy interval (bs, be), ensure the meeting does not overlap.
# The meeting (start, start + duration) either ends before bs or starts after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Diana's busy intervals:
# 12:00 to 13:30 -> [720, 810]
# 14:00 to 15:00 -> [840, 900]
# 16:30 to 17:00 -> [990, 1020]
diana_busy = [(720, 810), (840, 900), (990, 1020)]
add_busy_constraints(diana_busy)

# Rebecca's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 11:30 -> [600, 690]
# 13:00 to 13:30 -> [780, 810]
# 14:30 to 15:00 -> [870, 900]
rebecca_busy = [(540, 570), (600, 690), (780, 810), (870, 900)]
add_busy_constraints(rebecca_busy)

# Madison's busy intervals:
# 9:30 to 10:30  -> [570, 630]
# 11:00 to 12:30 -> [660, 750]
# 13:30 to 15:00 -> [810, 900]
# 15:30 to 16:30 -> [930, 990]
madison_busy = [(570, 630), (660, 750), (810, 900), (930, 990)]
add_busy_constraints(madison_busy)

# Carol's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 11:30 -> [660, 690]
# 12:00 to 14:00 -> [720, 840]
# 14:30 to 15:00 -> [870, 900]
# 16:00 to 17:00 -> [960, 1020]
carol_busy = [(540, 570), (600, 630), (660, 690), (720, 840), (870, 900), (960, 1020)]
add_busy_constraints(carol_busy)

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
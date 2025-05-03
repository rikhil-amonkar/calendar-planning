from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Hannah's preference: she does not want to meet before 14:30.
# 14:30 is 870 minutes from midnight.
solver.add(start >= 870)

# Helper function to add busy interval constraints.
# For a busy interval (bs, be), the meeting (start, start+duration)
# must either finish by bs or start at/after be.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Michael's busy intervals:
# 16:00 to 17:00 -> [960, 1020]
michael_busy = [(960, 1020)]
add_busy_constraints(michael_busy)

# Hannah's busy intervals:
# 9:30 to 10:30   -> [570, 630]
# 12:00 to 12:30  -> [720, 750]
# 13:30 to 14:00  -> [810, 840]
# 15:30 to 16:00  -> [930, 960]
# 16:30 to 17:00  -> [990, 1020]
hannah_busy = [(570, 630), (720, 750), (810, 840), (930, 960), (990, 1020)]
add_busy_constraints(hannah_busy)

# Brenda's busy intervals:
# 9:30 to 11:30   -> [570, 690]
# 12:00 to 13:00  -> [720, 780]
# 13:30 to 14:30  -> [810, 870]
# 15:00 to 17:00  -> [900, 1020]
brenda_busy = [(570, 690), (720, 780), (810, 870), (900, 1020)]
add_busy_constraints(brenda_busy)

# Anthony's busy intervals:
# 9:00 to 11:00   -> [540, 660]
# 12:00 to 12:30  -> [720, 750]
# 13:30 to 14:00  -> [810, 840]
# 15:30 to 16:30  -> [930, 990]
anthony_busy = [(540, 660), (720, 750), (810, 840), (930, 990)]
add_busy_constraints(anthony_busy)

# Check for a valid meeting time.
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
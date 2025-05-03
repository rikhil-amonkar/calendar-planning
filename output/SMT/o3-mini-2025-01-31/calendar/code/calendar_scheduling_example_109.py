from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time in minutes from midnight.
# Standard work hours: 9:00 (540) to 17:00 (1020),
# Meeting duration: 30 minutes.
# Additionally, Theresa does not want to meet after 12:00,
# so the meeting must finish by 12:00 (i.e., start + 30 <= 720).
start = Int('start')
solver.add(start >= 540, start + 30 <= 720)

# Helper function to add constraints ensuring the meeting does not overlap a busy interval.
# For each busy interval (busy_start, busy_end), the meeting (from start to start+30)
# must either finish before the busy interval begins or start after it ends.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + 30 <= busy_start, start >= busy_end))

# Marie's busy intervals:
#   11:00 to 11:30 -> [660, 690]
#   15:00 to 16:30 -> [900, 990]
marie_busy = [(660, 690), (900, 990)]
add_busy_constraints(marie_busy)

# Janice's busy intervals:
#   12:30 to 13:00 -> [750, 780]
#   13:30 to 15:00 -> [810, 900]
janice_busy = [(750, 780), (810, 900)]
add_busy_constraints(janice_busy)

# Elijah's busy intervals:
#   10:00 to 13:00 -> [600, 780]
#   14:30 to 15:00 -> [870, 900]
#   16:00 to 16:30 -> [960, 990]
elijah_busy = [(600, 780), (870, 900), (960, 990)]
add_busy_constraints(elijah_busy)

# Theresa's busy intervals:
#   9:30 to 10:30  -> [570, 630]
#   12:00 to 13:00 -> [720, 780]
#   13:30 to 14:00 -> [810, 840]
#   14:30 to 15:00 -> [870, 900]
#   15:30 to 16:00 -> [930, 960]
#   16:30 to 17:00 -> [990, 1020]
theresa_busy = [(570, 630), (720, 780), (810, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(theresa_busy)

# Check if there is a valid meeting slot and print it in HH:MM format.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + 30
    start_hour, start_min = meeting_start // 60, meeting_start % 60
    end_hour, end_min = meeting_end // 60, meeting_end % 60
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
        start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")
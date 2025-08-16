from z3 import *

# Create a solver instance
solver = Solver()

# Define the meeting start time (in minutes from midnight).
# For example, 9:00 is 540, 17:00 is 1020.
x = Int('x')

# Add constraints:
# 1. Meeting must be entirely within work hours [9:00, 17:00],
#    so x >= 9:00 (540) and x + 30 <= 17:00 (1020).
# 2. Margaret does not want to meet before 14:30 (870).
solver.add(x >= 870, x + 30 <= 1020)

# Busy intervals for every participant given as (start, end) in minutes from midnight.
# (For instance, 10:30 is 10*60+30 = 630).
busy_intervals = [
    # Shirley's busy times:
    (10*60+30, 11*60+0),    # 10:30 to 11:00
    (12*60+0, 12*60+30),     # 12:00 to 12:30

    # Jacob's busy times:
    (9*60+0, 9*60+30),      # 9:00 to 9:30
    (10*60+0, 10*60+30),     # 10:00 to 10:30
    (11*60+0, 11*60+30),     # 11:00 to 11:30
    (12*60+30, 13*60+30),    # 12:30 to 13:30
    (14*60+30, 15*60+0),     # 14:30 to 15:00

    # Stephen's busy times:
    (11*60+30, 12*60+0),     # 11:30 to 12:00
    (12*60+30, 13*60+0),     # 12:30 to 13:00

    # Margaret's busy times:
    (9*60+0, 9*60+30),       # 9:00 to 9:30
    (10*60+30, 12*60+30),     # 10:30 to 12:30
    (13*60+0, 13*60+30),      # 13:00 to 13:30
    (15*60+0, 15*60+30),      # 15:00 to 15:30
    (16*60+30, 17*60+0),      # 16:30 to 17:00

    # Mason's busy times:
    (9*60+0, 10*60+0),       # 9:00 to 10:00
    (10*60+30, 11*60+0),      # 10:30 to 11:00
    (11*60+30, 12*60+30),     # 11:30 to 12:30
    (13*60+0, 13*60+30),      # 13:00 to 13:30
    (14*60+0, 14*60+30),      # 14:00 to 14:30
    (16*60+30, 17*60+0)       # 16:30 to 17:00
]

# For each busy interval, ensure the meeting does not overlap with it.
# The meeting, which spans [x, x+30), must either finish on or before a busy interval starts,
# or start on or after the busy interval ends.
for start, end in busy_intervals:
    solver.add(Or(x + 30 <= start, x >= end))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[x].as_long()
    meeting_end = meeting_start + 30

    # Convert minutes to HH:MM (24-hour format)
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: {:02d}:{:02d}".format(start_hour, start_min))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_min))
else:
    print("No solution found")
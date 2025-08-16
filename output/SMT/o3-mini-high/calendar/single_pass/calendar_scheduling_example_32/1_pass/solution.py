from z3 import *

# Meeting duration in minutes
duration = 30

# Represent time as minutes from midnight.
# Work hours: 9:00 (540) to 17:00 (1020)
# Frank's additional constraint: no meetings after 9:30 (570) on Monday.
start = Int('start')
solver = Solver()

# Ensure the meeting is within work hours.
solver.add(start >= 540)       # not before 9:00
solver.add(start + duration <= 1020)  # must finish by 17:00

# Frank’s personal constraint: meeting must finish by 9:30.
solver.add(start + duration <= 570)

# Busy intervals for each participant (all times in minutes from midnight):
# Emily busy: 10:00-10:30, 11:30-12:30, 14:00-15:00, 16:00-16:30
# Melissa busy: 9:30-10:00, 14:30-15:00
# Frank busy: 10:00-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:00-16:00, 16:30-17:00
busy_intervals = [
    # Emily
    (600, 630),   # 10:00 to 10:30
    (690, 750),   # 11:30 to 12:30
    (840, 900),   # 14:00 to 15:00
    (960, 990),   # 16:00 to 16:30
    # Melissa
    (570, 600),   # 9:30 to 10:00
    (870, 900),   # 14:30 to 15:00
    # Frank
    (600, 630),   # 10:00 to 10:30
    (660, 690),   # 11:00 to 11:30
    (750, 780),   # 12:30 to 13:00
    (810, 870),   # 13:30 to 14:30
    (900, 960),   # 15:00 to 16:00
    (990, 1020)   # 16:30 to 17:00
]

# Ensure the meeting does not overlap with any busy interval.
# For each busy interval (b_start, b_end),
# the meeting (start to start+duration) must either finish before b_start or start after b_end.
for busy_start, busy_end in busy_intervals:
    solver.add(Or(start + duration <= busy_start, start >= busy_end))

if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    
    # Helper function to convert minutes to "HH:MM" format.
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"
    
    # Output the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", minutes_to_time(meeting_start))
    print("End Time:", minutes_to_time(meeting_end))
else:
    print("No solution found.")
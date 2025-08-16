from z3 import *

# We represent time as minutes from midnight.
# Since work hours are 9:00 to 17:00 and Janice prefers before 13:00,
# we restrict the meeting to start at or after 9:00 (540 minutes)
# and end by 13:00 (780 minutes).
# The meeting duration is 30 minutes.

meeting_start = Int("meeting_start")
meeting_duration = 30
meeting_end = meeting_start + meeting_duration

s = Solver()

# Constraint: meeting must start no earlier than 9:00 and end by 13:00.
s.add(meeting_start >= 540)       # 9:00 AM
s.add(meeting_end <= 780)         # 13:00 (meeting end must be at or before 13:00)

# Busy intervals (in minutes after midnight) for each participant on Monday:
# Christine: 9:30-10:30, 12:00-12:30, 13:00-13:30, 14:30-15:00, 16:00-16:30
# Janice: (no busy intervals, but prefers meeting before 13:00)
# Bobby: 12:00-12:30, 14:30-15:00
# Elizabeth: 9:00-9:30, 11:30-13:00, 13:30-14:00, 15:00-15:30, 16:00-17:00
# Tyler: 9:00-11:00, 12:00-12:30, 13:00-13:30, 15:30-16:00, 16:30-17:00
# Edward: 9:00-9:30, 10:00-11:00, 11:30-14:00, 14:30-15:30, 16:00-17:00

busy_intervals = [
    # Christine's busy times
    (570, 630),   # 09:30 to 10:30
    (720, 750),   # 12:00 to 12:30
    (780, 810),   # 13:00 to 13:30
    (870, 900),   # 14:30 to 15:00
    (960, 990),   # 16:00 to 16:30

    # Bobby's busy times
    (720, 750),   # 12:00 to 12:30
    (870, 900),   # 14:30 to 15:00

    # Elizabeth's busy times
    (540, 570),   # 09:00 to 09:30
    (690, 780),   # 11:30 to 13:00
    (810, 840),   # 13:30 to 14:00
    (900, 930),   # 15:00 to 15:30
    (960, 1020),  # 16:00 to 17:00

    # Tyler's busy times
    (540, 660),   # 09:00 to 11:00
    (720, 750),   # 12:00 to 12:30
    (780, 810),   # 13:00 to 13:30
    (930, 960),   # 15:30 to 16:00
    (990, 1020),  # 16:30 to 17:00

    # Edward's busy times
    (540, 570),   # 09:00 to 09:30
    (600, 660),   # 10:00 to 11:00
    (690, 840),   # 11:30 to 14:00
    (870, 930),   # 14:30 to 15:30
    (960, 1020)   # 16:00 to 17:00
]

# For each busy interval, the meeting must not overlap it.
# That is, for each interval (b_start, b_end), either the meeting finishes by b_start
# or starts at/after b_end.
for (b_start, b_end) in busy_intervals:
    s.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    start_val = m[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Helper function to convert minutes to HH:MM format.
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    start_time_str = minutes_to_time(start_val)
    end_time_str = minutes_to_time(end_val)

    # Output in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + start_time_str)
    print("End Time: " + end_time_str)
else:
    print("No solution found.")
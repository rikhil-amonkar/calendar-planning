from z3 import *

# Meeting duration in minutes
duration = 30

# Define the meeting start time as an integer representing minutes after 9:00.
# It must be chosen such that the meeting ends by 17:00. Since the working day is 8 hours (480 minutes),
# meeting_start can be in [0, 480 - duration] i.e. [0, 450].
meeting = Int('meeting')
s = Solver()
s.add(meeting >= 0, meeting <= 450)

# Each busy interval is given as (start_minutes, end_minutes) relative to 9:00.
# For example, a meeting from 10:00 to 10:30 translates to (60, 90) because 10:00 is 60 minutes after 9:00.
busy_intervals = [
    # Emily's busy times
    (60, 90),    # 10:00 - 10:30
    (420, 450),  # 16:00 - 16:30

    # Maria's busy times
    (90, 120),   # 10:30 - 11:00
    (300, 330),  # 14:00 - 14:30

    # Carl's busy times
    (30, 60),    # 9:30 - 10:00
    (90, 210),   # 10:30 - 12:30
    (270, 300),  # 13:30 - 14:00
    (330, 390),  # 14:30 - 15:30
    (420, 480),  # 16:00 - 17:00

    # David's busy times
    (30, 120),   # 9:30 - 11:00
    (150, 180),  # 11:30 - 12:00
    (210, 270),  # 12:30 - 13:30
    (300, 360),  # 14:00 - 15:00
    (420, 480),  # 16:00 - 17:00

    # Frank's busy times
    (30, 90),    # 9:30 - 10:30
    (120, 150),  # 11:00 - 11:30
    (210, 270),  # 12:30 - 13:30
    (330, 480)   # 14:30 - 17:00
]

# For each busy interval, add a constraint so that the meeting time does not overlap with the busy interval.
# The meeting [m, m+duration) is non-overlapping with a busy interval [busy_start, busy_end) if:
#   meeting_end <= busy_start  OR  busy_end <= meeting_start
for (busy_start, busy_end) in busy_intervals:
    s.add(Or(meeting + duration <= busy_start, meeting >= busy_end))

# Try to find a valid meeting time that satisfies all constraints.
if s.check() == sat:
    model = s.model()
    meeting_start = model[meeting].as_long()

    # Convert meeting_start (minutes after 9:00) to an actual time.
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60

    meeting_end = meeting_start + duration
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60

    # Output the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: {:02d}:{:02d}".format(start_hour, start_minute))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_minute))
else:
    print("No solution found")
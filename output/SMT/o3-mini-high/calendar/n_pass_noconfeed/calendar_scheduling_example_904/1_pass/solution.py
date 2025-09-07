from z3 import *

# Define our variables:
# day: 1 = Monday, 2 = Tuesday, 3 = Wednesday, 4 = Thursday, 5 = Friday
# start: meeting start time in minutes from 9:00, meeting duration is fixed to 30 minutes.
day = Int('day')
start = Int('start')
duration = 30

solver = Solver()

# Working hours constraints:
# Meeting must start at or after 9:00 (0 minutes) and finish by 17:00 (480 minutes after 9:00)
solver.add(start >= 0, start + duration <= 480)
solver.add(And(day >= 1, day <= 5))

# Preference constraints:
# Daniel would rather not meet on Wednesday (3) or Thursday (4)
solver.add(day != 3, day != 4)

# Bradley does not want to meet on Monday (1) or Friday (5)
solver.add(day != 1, day != 5)
# Bradley does not want Tuesday meetings before 12:00 (i.e. 3 hours after 9:00 => start >= 180 when day == 2)
solver.add(Implies(day == 2, start >= 180))

# Busy time intervals for Daniel and Bradley are expressed in minutes from 9:00.
# Each tuple is (day, busy_start, busy_end).
busy_intervals_daniel = [
    # Monday
    (1, 30, 90),    # 9:30-10:30
    (1, 180, 210),  # 12:00-12:30
    (1, 240, 300),  # 13:00-14:00
    (1, 330, 360),  # 14:30-15:00
    (1, 390, 420),  # 15:30-16:00
    # Tuesday
    (2, 120, 180),  # 11:00-12:00
    (2, 240, 270),  # 13:00-13:30
    (2, 390, 420),  # 15:30-16:00
    (2, 450, 480),  # 16:30-17:00
    # Wednesday
    (3, 0, 60),     # 9:00-10:00
    (3, 300, 330),  # 14:00-14:30
    # Thursday
    (4, 90, 120),   # 10:30-11:00
    (4, 180, 240),  # 12:00-13:00
    (4, 330, 360),  # 14:30-15:00
    (4, 390, 420),  # 15:30-16:00
    # Friday
    (5, 0, 30),     # 9:00-9:30
    (5, 150, 180),  # 11:30-12:00
    (5, 240, 270),  # 13:00-13:30
    (5, 450, 480)   # 16:30-17:00
]

busy_intervals_bradley = [
    # Monday
    (1, 30, 120),   # 9:30-11:00
    (1, 90, 120),   # 11:30-12:00
    (1, 150, 180),  # 12:30-13:00
    (1, 300, 360),  # 14:00-15:00
    # Tuesday
    (2, 90, 120),   # 10:30-11:00
    (2, 180, 240),  # 12:00-13:00
    (2, 270, 300),  # 13:30-14:00
    (2, 390, 450),  # 15:30-16:30
    # Wednesday
    (3, 0, 60),     # 9:00-10:00
    (3, 120, 240),  # 11:00-13:00
    (3, 270, 300),  # 13:30-14:00
    (3, 330, 480),  # 14:30-17:00
    # Thursday
    (4, 0, 210),    # 9:00-12:30
    (4, 270, 300),  # 13:30-14:00
    (4, 330, 360),  # 14:30-15:00
    (4, 390, 450),  # 15:30-16:30
    # Friday
    (5, 0, 30),     # 9:00-9:30
    (5, 60, 210),   # 10:00-12:30
    (5, 240, 270),  # 13:00-13:30
    (5, 300, 330),  # 14:00-14:30
    (5, 390, 450)   # 15:30-16:30
]

# For each busy interval, if the meeting is scheduled on that day, then the meeting must not overlap the busy interval.
for (d, b_start, b_end) in busy_intervals_daniel:
    # If meeting is on day d, then either the meeting ends before the busy interval starts,
    # or starts after the busy interval ends.
    solver.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))

for (d, b_start, b_end) in busy_intervals_bradley:
    solver.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))

# Find a solution.
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration

    # Map day number to day name.
    day_names = {1: "Monday", 2: "Tuesday", 3: "Wednesday", 4: "Thursday", 5: "Friday"}
    day_str = day_names[meeting_day]

    # Convert meeting start/end from minutes (offset from 9:00) to HH:MM format.
    def to_hhmm(minutes_offset):
        total_minutes = 9 * 60 + minutes_offset  # 9:00 is the baseline.
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = to_hhmm(meeting_start)
    end_str = to_hhmm(meeting_end)

    # Output the meeting time and day in the format "Day HH:MM:HH:MM"
    print(f"{day_str} {start_str}:{end_str}")
else:
    print("No meeting time found.")
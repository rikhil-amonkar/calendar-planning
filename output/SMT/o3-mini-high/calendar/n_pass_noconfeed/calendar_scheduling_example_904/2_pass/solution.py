#!/usr/bin/env python3
from z3 import *

# --- Define variables ---
# day: 1 = Monday, 2 = Tuesday, 3 = Wednesday, 4 = Thursday, 5 = Friday
# start: meeting start time in minutes from 9:00 AM
# end: meeting end time in minutes from 9:00 AM (we enforce end = start + duration)
day  = Int('day')
start = Int('start')
end   = Int('end')
duration = 30  # Meeting duration fixed to 30 minutes

solver = Solver()

# --- Working hours constraints ---
# The meeting must start at or after 9:00 (0 minutes) and finish by 17:00 (480 minutes after 9:00)
solver.add(start >= 0, end <= 480)
solver.add(end == start + duration)
solver.add(And(day >= 1, day <= 5))

# --- Preference constraints ---
# Daniel would rather not meet on Wednesday (3) or Thursday (4)
solver.add(day != 3, day != 4)
# Bradley does not want to meet on Monday (1) or Friday (5)
solver.add(day != 1, day != 5)
# Bradley does not want Tuesday meetings before 12:00 (i.e. 3 hours after 9:00 => start >= 180 when day == 2)
solver.add(Implies(day == 2, start >= 180))

# --- Busy time intervals, expressed in minutes from 9:00 ---
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

# --- Busy interval constraints ---
# For each busy interval on a given day, if the meeting is on that day then the meeting time must
# either finish before the busy interval starts or start after the busy interval ends.
for (d, b_start, b_end) in busy_intervals_daniel:
    solver.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

for (d, b_start, b_end) in busy_intervals_bradley:
    solver.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# --- Find and output a solution ---
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start].as_long()
    meeting_end   = model[end].as_long()

    # Map day number to day name.
    day_names = {1: "Monday", 2: "Tuesday", 3: "Wednesday", 4: "Thursday", 5: "Friday"}
    day_str = day_names[meeting_day]

    # Helper function to convert offset minutes (from 9:00) to HH:MM format.
    def to_hhmm(minutes_offset):
        total_minutes = 9 * 60 + minutes_offset  # 9:00 AM is the baseline.
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = to_hhmm(meeting_start)
    end_str = to_hhmm(meeting_end)

    # Create the plan dictionary in the expected format.
    plan = {
        'day': day_str,
        'time_range': f'{{{start_str}:{end_str}}}'
    }
    print(plan)
else:
    print("No meeting time found.")
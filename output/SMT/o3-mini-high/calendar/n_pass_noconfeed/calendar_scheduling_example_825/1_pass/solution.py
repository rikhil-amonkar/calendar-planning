from z3 import *

# Define meeting duration (in minutes)
meeting_duration = 60

# Day encoding: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
day = Int('day')
start = Int('start')  # start time in minutes offset from 9:00

s = Solver()

# The meeting must start within work hours: [9:00, 17:00 - meeting_duration]
s.add(start >= 0, start <= 480 - meeting_duration)

# The meeting day must be one of Monday (0), Tuesday (1), Wednesday (2), Thursday (3)
s.add(Or(day == 0, day == 1, day == 2, day == 3))

# Additional constraint: Philip cannot meet on Wednesday (day == 2)
s.add(day != 2)

# Busy intervals for each participant are given as (day, busy_start, busy_end)
# Here busy_start and busy_end are minutes offset from 9:00.
busy_intervals = []

# Laura's busy slots:
# Monday: 10:30-11:00, 12:30-13:00, 14:30-15:30, 16:00-17:00
busy_intervals += [
    (0, 90, 120),
    (0, 210, 240),
    (0, 330, 390),
    (0, 420, 480)
]
# Tuesday: 9:30-10:00, 11:00-11:30, 13:00-13:30, 14:30-15:00, 16:00-17:00
busy_intervals += [
    (1, 30, 60),
    (1, 120, 150),
    (1, 240, 270),
    (1, 330, 360),
    (1, 420, 480)
]
# Wednesday: 11:30-12:00, 12:30-13:00, 15:30-16:30
busy_intervals += [
    (2, 90 + 60, 120 + 60),  # 11:30 is 150, 12:00 is 180
    (2, 150 + 60, 180 + 60),  # 12:30 is 210, 13:00 is 240
    (2, 390, 450)            # 15:30-16:30: 15:30 is 390, 16:30 is 450
]
# Thursday: 10:30-11:00, 12:00-13:30, 15:00-15:30, 16:00-16:30
busy_intervals += [
    (3, 90, 120),
    (3, 180, 270),
    (3, 360, 390),
    (3, 420, 450)
]

# Philip's busy slots:
# Monday: 9:00-17:00
busy_intervals += [
    (0, 0, 480)
]
# Tuesday: 9:00-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-16:30
busy_intervals += [
    (1, 0, 120),
    (1, 150, 180),
    (1, 240, 270),
    (1, 300, 330),
    (1, 360, 450)
]
# Wednesday: 9:00-10:00, 11:00-12:00, 12:30-16:00, 16:30-17:00
busy_intervals += [
    (2, 0, 60),
    (2, 120, 180),
    (2, 150, 420),
    (2, 450, 480)
]
# Thursday: 9:00-10:30, 11:00-12:30, 13:00-17:00
busy_intervals += [
    (3, 0, 90),
    (3, 120, 150),
    (3, 240, 480)
]

# For any busy interval on the meeting day, the meeting must not overlap.
# Overlap is avoided if: meeting_end <= busy_start OR meeting_start >= busy_end.
for (bd, b_start, b_end) in busy_intervals:
    s.add(Implies(day == bd, Or(start + meeting_duration <= b_start, start >= b_end)))

# Check for a solution
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    
    # Convert chosen start time (minutes offset from 9:00) into an actual time.
    # Work starts at 9:00 (i.e., 9*60 minutes).
    actual_start = 9 * 60 + chosen_start
    actual_end = actual_start + meeting_duration
    
    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    
    meeting_time_str = f"{format_time(actual_start)}:{format_time(actual_end)}"
    meeting_day_str = day_map[chosen_day]
    
    print(meeting_time_str, meeting_day_str)
else:
    print("No suitable meeting time found.")
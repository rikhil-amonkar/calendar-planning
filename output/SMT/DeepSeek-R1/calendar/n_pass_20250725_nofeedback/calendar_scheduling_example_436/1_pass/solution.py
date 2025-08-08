from z3 import *

def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

participants = {
    "Patrick": ["13:30 to 14:00", "14:30 to 15:00"],
    "Shirley": ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 12:30", "14:30 to 15:00", "16:00 to 17:00"],
    "Jeffrey": ["9:00 to 9:30", "10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "16:00 to 17:00"],
    "Gloria": ["11:30 to 12:00", "15:00 to 15:30"],
    "Nathan": ["9:00 to 9:30", "10:30 to 12:00", "14:00 to 17:00"],
    "Angela": ["9:00 to 9:30", "10:00 to 11:00", "12:30 to 15:00", "15:30 to 16:30"],
    "David": ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 14:00", "14:30 to 16:30"]
}

intervals = []
for person, busy_list in participants.items():
    for interval in busy_list:
        parts = interval.split(' to ')
        start_str = parts[0].strip()
        end_str = parts[1].strip()
        start_min = time_str_to_minutes(start_str)
        end_min = time_str_to_minutes(end_str)
        intervals.append((start_min, end_min))

s = Solver()
S = Int('S')
s.add(S >= 0, S <= 15)

for (a, b) in intervals:
    s.add(Or(30 * S + 30 <= a, 30 * S >= b))

if s.check() == sat:
    m = s.model()
    slot = m[S].as_long()
    total_minutes = slot * 30
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    end_minutes = total_minutes + 30
    end_hours = 9 + end_minutes // 60
    end_minutes_rem = end_minutes % 60
    end_time = f"{end_hours:02d}:{end_minutes_rem:02d}"
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")
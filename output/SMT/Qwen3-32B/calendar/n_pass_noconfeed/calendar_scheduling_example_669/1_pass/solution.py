from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

day = Int('day')
start = Int('start')

# Day must be Monday (0) or Tuesday (1)
s.add(Or(day == 0, day == 1))

# Doris is busy all day on Tuesday, so day must be Monday
s.add(day == 0)

# Start time constraints for Monday (9:00 to 14:00)
s.add(And(start >= 540, start <= 810))  # 540 = 9:00, 810 = 13:30 (start +30 <= 14:00)
s.add(start + 30 <= 1020)  # Ensure meeting ends by 17:00

# Doris's busy intervals on Monday
busy_intervals = [
    (540, 690),  # 9:00-11:30
    (720, 750),  # 12:00-12:30
    (810, 960),  # 13:30-16:00
    (990, 1020)  # 16:30-17:00
]

for b_start, b_end in busy_intervals:
    s.add(Or(start + 30 <= b_start, start >= b_end))

if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + 30
    day_str = "Monday" if day_val == 0 else "Tuesday"
    start_time = to_time(start_val)
    end_time = to_time(end_val)
    print(f"{day_str} {start_time}:{end_time}")
else:
    print("No solution found")
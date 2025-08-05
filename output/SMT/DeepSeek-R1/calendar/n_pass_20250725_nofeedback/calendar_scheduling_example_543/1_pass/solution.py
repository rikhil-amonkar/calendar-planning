from z3 import *

def time_to_minutes(time_str):
    h, m = time_str.split(':')
    total = int(h) * 60 + int(m)
    return total - 9 * 60  # Subtract 9:00 in minutes (540)

# Busy intervals for James and John
intervals = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),  # James
    (time_to_minutes("14:30"), time_to_minutes("15:00")),  # James
    (time_to_minutes("9:30"), time_to_minutes("11:00")),   # John
    (time_to_minutes("11:30"), time_to_minutes("12:00")),  # John
    (time_to_minutes("12:30"), time_to_minutes("13:30")),  # John
    (time_to_minutes("14:30"), time_to_minutes("16:30"))   # John
]

s = Solver()
start = Int('start')
s.add(0 <= start, start <= 420)  # Meeting must start between 0 and 420 minutes (inclusive)

for (b_start, b_end) in intervals:
    s.add(Or(start + 60 <= b_start, start >= b_end))

if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    
    # Convert start_val back to HH:MM format
    total_minutes_start = start_val
    abs_start_minutes = 9 * 60 + total_minutes_start
    start_hour = abs_start_minutes // 60
    start_minute = abs_start_minutes % 60
    start_time_str = f"{start_hour:02d}:{start_minute:02d}"
    
    # Calculate end time
    end_val = start_val + 60
    abs_end_minutes = 9 * 60 + end_val
    end_hour = abs_end_minutes // 60
    end_minute = abs_end_minutes % 60
    end_time_str = f"{end_hour:02d}:{end_minute:02d}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found")
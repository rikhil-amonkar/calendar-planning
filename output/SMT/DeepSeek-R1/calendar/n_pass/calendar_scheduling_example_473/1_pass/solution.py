from z3 import *

def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return (hours - 9) * 60 + minutes

def main():
    busy_intervals = []
    
    # Gregory
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("9:30")))
    busy_intervals.append((time_str_to_minutes("11:30"), time_str_to_minutes("12:00")))
    
    # Jonathan
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("9:30")))
    busy_intervals.append((time_str_to_minutes("12:00"), time_str_to_minutes("12:30")))
    busy_intervals.append((time_str_to_minutes("13:00"), time_str_to_minutes("13:30")))
    busy_intervals.append((time_str_to_minutes("15:00"), time_str_to_minutes("16:00")))
    busy_intervals.append((time_str_to_minutes("16:30"), time_str_to_minutes("17:00")))
    
    # Barbara
    busy_intervals.append((time_str_to_minutes("10:00"), time_str_to_minutes("10:30")))
    busy_intervals.append((time_str_to_minutes("13:30"), time_str_to_minutes("14:00")))
    
    # Jesse
    busy_intervals.append((time_str_to_minutes("10:00"), time_str_to_minutes("11:00")))
    busy_intervals.append((time_str_to_minutes("12:30"), time_str_to_minutes("14:30")))
    
    # Alan
    busy_intervals.append((time_str_to_minutes("9:30"), time_str_to_minutes("11:00")))
    busy_intervals.append((time_str_to_minutes("11:30"), time_str_to_minutes("12:30")))
    busy_intervals.append((time_str_to_minutes("13:00"), time_str_to_minutes("15:30")))
    busy_intervals.append((time_str_to_minutes("16:00"), time_str_to_minutes("17:00")))
    
    # Nicole
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("10:30")))
    busy_intervals.append((time_str_to_minutes("11:30"), time_str_to_minutes("12:00")))
    busy_intervals.append((time_str_to_minutes("12:30"), time_str_to_minutes("13:30")))
    busy_intervals.append((time_str_to_minutes("14:00"), time_str_to_minutes("17:00")))
    
    # Catherine
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("10:30")))
    busy_intervals.append((time_str_to_minutes("12:00"), time_str_to_minutes("13:30")))
    busy_intervals.append((time_str_to_minutes("15:00"), time_str_to_minutes("15:30")))
    busy_intervals.append((time_str_to_minutes("16:00"), time_str_to_minutes("16:30")))
    
    s = Solver()
    start_time = Int('start_time')
    s.add(start_time >= 0)
    s.add(start_time <= 450)  # 450 minutes from 9:00 is 16:30, ensuring meeting ends by 17:00
    
    for (s_busy, e_busy) in busy_intervals:
        s.add(Or(start_time + 30 <= s_busy, start_time >= e_busy))
    
    if s.check() == sat:
        m = s.model()
        start_val = m[start_time].as_long()
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_str = f"{hours}:{minutes:02d}"
        end_val = start_val + 30
        hours_end = 9 + end_val // 60
        minutes_end = end_val % 60
        end_str = f"{hours_end}:{minutes_end:02d}"
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
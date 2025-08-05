import re
from z3 import *

def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def parse_busy_string(s):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    pattern = '|'.join(days)
    tokens = re.split(f'({pattern})', s)
    busy_dict = {day: [] for day in days}
    for i in range(len(tokens)):
        if tokens[i] in days:
            day_name = tokens[i]
            if i + 1 < len(tokens):
                content = tokens[i + 1]
                intervals = []
                parts = content.split(',')
                for part in parts:
                    part = part.strip()
                    if part == '':
                        continue
                    if ' to ' in part:
                        times = part.split(' to ', 1)
                        t1 = times[0].strip()
                        t2 = times[1].strip()
                        try:
                            start_min = time_to_minutes(t1)
                            end_min = time_to_minutes(t2)
                            intervals.append((start_min, end_min))
                        except:
                            continue
                busy_dict[day_name] = intervals
    return busy_dict

def main():
    diane_input = "Diane is busy on Monday during 12:00 to 12:30, 15:00 to 15:30, Tuesday during 10:00 to 11:00, 11:30 to 12:00, 12:30 to 13:00, 16:00 to 17:00, Wednesday during 9:00 to 9:30, 14:30 to 15:00, 16:30 to 17:00, Thursday during 15:30 to 16:30, Friday during 9:30 to 11:30, 14:30 to 15:00, 16:00 to 17:00"
    matthew_input = "Matthew has meetings on Monday during 9:00 to 10:00, 10:30 to 17:00, Tuesday during 9:00 to 17:00, Wednesday during 9:00 to 11:00, 12:00 to 14:30, 16:00 to 17:00, Thursday during 9:00 to 16:00, Friday during 9:00 to 17:00"
    
    diane_busy = parse_busy_string(diane_input)
    matthew_busy = parse_busy_string(matthew_input)
    
    day = Int('day')
    start_minutes = Int('start_minutes')
    s = Solver()
    
    s.add(day >= 0, day <= 4)
    s.add(start_minutes >= 540)
    s.add(start_minutes <= 960)
    
    s.add(Implies(day == 2, start_minutes >= 750))
    
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    for d in range(5):
        day_name = day_names[d]
        if day_name in diane_busy:
            for (bs, be) in diane_busy[day_name]:
                s.add(Implies(day == d, Or(start_minutes + 60 <= bs, start_minutes >= be)))
        if day_name in matthew_busy:
            for (bs, be) in matthew_busy[day_name]:
                s.add(Implies(day == d, Or(start_minutes + 60 <= bs, start_minutes >= be)))
    
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start_minutes].as_long()
        end_val = start_val + 60
        day_name = day_names[d_val]
        start_hour = start_val // 60
        start_minute = start_val % 60
        end_hour = end_val // 60
        end_minute = end_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
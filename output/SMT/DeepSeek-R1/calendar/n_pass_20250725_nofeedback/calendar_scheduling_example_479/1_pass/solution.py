from z3 import *

def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return hours, mins

def main():
    busy_participants = {
        "Joshua": ["11:00 to 12:30", "13:30 to 14:30", "16:30 to 17:00"],
        "Jerry": ["9:00 to 9:30", "10:30 to 12:00", "12:30 to 13:00", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 16:00"],
        "Jesse": ["9:00 to 9:30", "10:30 to 12:00", "12:30 to 13:00", "14:30 to 15:00", "15:30 to 16:30"],
        "Kenneth": ["10:30 to 12:30", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 16:00", "16:30 to 17:00"]
    }
    
    intervals_list = []
    for participant, interval_strs in busy_participants.items():
        for interval_str in interval_strs:
            parts = interval_str.split(' to ')
            if len(parts) < 2:
                continue
            start_str = parts[0].strip()
            end_str = parts[1].strip()
            start_min = time_str_to_minutes(start_str)
            end_min = time_str_to_minutes(end_str)
            intervals_list.append((start_min, end_min))
    
    s = Solver()
    start_var = Int('start')
    s.add(start_var >= 0)
    s.add(start_var <= 420)
    
    for (b_start, b_end) in intervals_list:
        s.add(Or(start_var + 60 <= b_start, start_var >= b_end))
    
    if s.check() == sat:
        model = s.model()
        start_val = model[start_var].as_long()
        start_hour, start_minute = minutes_to_time(start_val)
        end_hour, end_minute = minutes_to_time(start_val + 60)
        
        start_time_str = f"{start_hour}:{start_minute:02d}"
        end_time_str = f"{end_hour}:{end_minute:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
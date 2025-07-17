from z3 import *

def main():
    # Hardcoded busy intervals for Nancy and Jose in (hr, min, hr, min) format per day
    nancy_busy = {
        'Monday': [(10, 0, 10, 30), (11, 30, 12, 30), (13, 30, 14, 0), (14, 30, 15, 30), (16, 0, 17, 0)],
        'Tuesday': [(9, 30, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 0, 13, 30), (15, 30, 16, 0)],
        'Wednesday': [(10, 0, 11, 30), (13, 30, 16, 0)]
    }
    
    jose_busy = {
        'Monday': [(9, 0, 17, 0)],
        'Tuesday': [(9, 0, 17, 0)],
        'Wednesday': [(9, 0, 9, 30), (10, 0, 12, 30), (13, 30, 14, 30), (15, 0, 17, 0)]
    }
    
    # Map days to indices and absolute minute offsets
    day_index = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
    minutes_per_day = 24 * 60  # 1440 minutes in a day
    
    # Convert busy intervals to absolute minutes
    def convert_intervals(busy_dict):
        intervals = []
        for day, day_intervals in busy_dict.items():
            idx = day_index[day]
            for (start_hr, start_min, end_hr, end_min) in day_intervals:
                start_abs = idx * minutes_per_day + start_hr * 60 + start_min
                end_abs = idx * minutes_per_day + end_hr * 60 + end_min
                intervals.append((start_abs, end_abs))
        return intervals
    
    nancy_intervals = convert_intervals(nancy_busy)
    jose_intervals = convert_intervals(jose_busy)
    
    # Define Z3 variables and solver
    d = Int('d')
    t = Int('t')
    base = d * minutes_per_day + 9 * 60 + t  # 9:00 is 540 minutes
    
    opt = Optimize()
    
    # Constraints for d and t
    opt.add(Or(d == 0, d == 1, d == 2))
    opt.add(t >= 0)
    opt.add(t <= 450)  # 450 minutes after 9:00 is 16:30, ensuring meeting ends by 17:00
    
    # Non-overlap constraints for Nancy
    for (s_busy, e_busy) in nancy_intervals:
        opt.add(Or(base + 30 <= s_busy, base >= e_busy))
    
    # Non-overlap constraints for Jose
    for (s_busy, e_busy) in jose_intervals:
        opt.add(Or(base + 30 <= s_busy, base >= e_busy))
    
    # Minimize the base time for earliest meeting
    opt.minimize(base)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m[d].as_long()
        t_val = m[t].as_long()
        base_val = d_val * minutes_per_day + 540 + t_val
        
        # Convert base_val to day and time
        minutes_in_day = base_val % minutes_per_day
        hour = minutes_in_day // 60
        minute = minutes_in_day % 60
        
        # Calculate end time
        end_minutes_in_day = minutes_in_day + 30
        end_hour = end_minutes_in_day // 60
        end_minute = end_minutes_in_day % 60
        
        # Map day index to name
        day_name = {0: 'Monday', 1: 'Tuesday', 2: 'Wednesday'}[d_val]
        
        # Format start and end times
        start_time = f"{hour}:{minute:02d}"
        end_time = f"{end_hour}:{end_minute:02d}"
        
        print(f"Day: {day_name}, Start Time: {start_time}, End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
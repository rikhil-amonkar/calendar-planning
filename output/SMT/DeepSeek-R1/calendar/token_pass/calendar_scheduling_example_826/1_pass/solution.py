from z3 import *

def main():
    # Define the busy intervals for each day in minutes from 9:00
    busy_intervals = [
        # Monday
        [(0, 30), (90, 120), (210, 240), (330, 390), (450, 480)],
        # Tuesday
        [(0, 120), (150, 180), (210, 390), (420, 480)],
        # Wednesday
        [(60, 120), (180, 240), (270, 420)],
        # Thursday
        [(30, 150), (180, 210), (240, 270), (300, 330), (450, 480)]
    ]
    day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Initialize Z3 solver and variables
    opt = Optimize()
    day = Int('day')
    start = Int('start')
    
    # Add constraints for day and start time
    opt.add(day >= 0, day <= 3)
    opt.add(start >= 0, start <= 450)  # 450 = 480 - 30
    
    # Add constraints for each day's busy intervals
    for idx, intervals in enumerate(busy_intervals):
        day_constraints = []
        for b_start, b_end in intervals:
            # Ensure no overlap with busy intervals
            day_constraints.append(Or(start + 30 <= b_start, start >= b_end))
        opt.add(If(day == idx, And(day_constraints), True))
    
    # Minimize day and start time lexicographically
    objective = day * 10000 + start
    opt.minimize(objective)
    
    # Check for solution and output
    if opt.check() == sat:
        m = opt.model()
        d = m[day].as_long()
        s_val = m[start].as_long()
        
        # Convert minutes to time strings
        start_total_minutes = s_val
        start_hour = 9 + start_total_minutes // 60
        start_minute = start_total_minutes % 60
        end_total_minutes = s_val + 30
        end_hour = 9 + end_total_minutes // 60
        end_minute = end_total_minutes % 60
        
        # Format output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"{day_names[d]} {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
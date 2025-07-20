from z3 import *

def main():
    # Busy intervals for Terry (in minutes from 9:00, as half-open intervals [start, end))
    terry_busy = {
        0: [(90, 120), (210, 300), (360, 480)],    # Monday
        1: [(30, 60), (90, 120), (300, 330), (420, 450)],  # Tuesday
        2: [(30, 90), (120, 180), (240, 270), (360, 420), (450, 480)],  # Wednesday
        3: [(30, 60), (180, 210), (240, 330), (420, 450)],  # Thursday
        4: [(0, 150), (180, 210), (270, 420), (450, 480)]   # Friday
    }
    
    # Busy intervals for Frances
    frances_busy = {
        0: [(30, 120), (150, 240), (300, 330), (360, 420)],  # Monday
        1: [(0, 30), (60, 90), (120, 180), (240, 330), (390, 450)],  # Tuesday
        2: [(30, 60), (90, 120), (150, 420), (450, 480)],  # Wednesday
        3: [(120, 210), (330, 480)],  # Thursday
        4: [(30, 90), (120, 210), (240, 420), (450, 480)]   # Friday
    }
    
    # Create Z3 variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Create solver and add constraints
    opt = Optimize()
    
    # Day must be between 0 (Monday) and 4 (Friday)
    opt.add(day >= 0, day <= 4)
    
    # Start time must be between 0 (9:00) and 450 (16:30) inclusive
    opt.add(start_time >= 0, start_time <= 450)
    
    # Add constraints for Terry's busy intervals
    for d, intervals in terry_busy.items():
        for (b_s, b_e) in intervals:
            # For the chosen day, the meeting must not overlap with any busy interval
            opt.add(Implies(day == d, Or(start_time + 30 <= b_s, start_time >= b_e)))
    
    # Add constraints for Frances's busy intervals
    for d, intervals in frances_busy.items():
        for (b_s, b_e) in intervals:
            opt.add(Implies(day == d, Or(start_time + 30 <= b_s, start_time >= b_e)))
    
    # Objective: minimize (day * 480 + start_time) to find the earliest slot
    objective = day * 480 + start_time
    opt.minimize(objective)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        s_val = m[start_time].as_long()
        
        # Convert day index to day name
        day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_str = day_names[d_val]
        
        # Convert start time in minutes to HH:MM format
        total_minutes = s_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = s_val + 30
        end_hours = 9 + end_minutes // 60
        end_minutes %= 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Day: {day_str}, Start: {start_str}, End: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
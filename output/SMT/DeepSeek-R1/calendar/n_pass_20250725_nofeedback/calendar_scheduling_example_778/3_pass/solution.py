from z3 import *

def main():
    # Blocked times in absolute minutes (from midnight) as (start, end) intervals
    susan_blocks = [
        [(12*60+30, 13*60), (13*60+30, 14*60)],  # Monday
        [(11*60+30, 12*60)],                      # Tuesday
        [(9*60+30, 10*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)]  # Wednesday
    ]
    
    sandra_blocks = [
        [(9*60, 13*60), (14*60, 15*60), (16*60, 16*60+30)],  # Monday
        [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)],  # Tuesday
        [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)]  # Wednesday
    ]
    
    # Create solver and variables
    s = Solver()
    day = Int('day')
    start_abs = Int('start_abs')  # Absolute start time in minutes from midnight
    
    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
    s.add(day >= 0, day <= 2)
    # Start time must be between 9:00 (540) and 16:30 (990) inclusive
    s.add(start_abs >= 540, start_abs <= 990)
    
    # For each day, add constraints that the meeting does not overlap with blocked times
    for d in range(3):
        constraints_for_day = []
        # Add constraints for Susan's blocked times
        for block in susan_blocks[d]:
            s_start, s_end = block
            constraints_for_day.append(Or(start_abs + 30 <= s_start, start_abs >= s_end))
        # Add constraints for Sandra's blocked times
        for block in sandra_blocks[d]:
            s_start, s_end = block
            constraints_for_day.append(Or(start_abs + 30 <= s_start, start_abs >= s_end))
        # Only apply constraints if the meeting is on this day
        s.add(Implies(day == d, And(constraints_for_day)))
    
    # Additional constraint: Sandra cannot meet on Monday after 16:00
    # This means the meeting must end by 16:00 (960 minutes) on Monday
    s.add(Implies(day == 0, start_abs + 30 <= 16*60))
    
    # First, try to avoid Tuesday (day=1) as per Susan's preference
    s.push()
    s.add(day != 1)
    
    if s.check() == sat:
        m = s.model()
    else:
        s.pop()
        s.check()
        m = s.model()
    
    # Extract the solution
    d_val = m[day].as_long()
    start_val = m[start_abs].as_long()
    end_val = start_val + 30
    
    # Convert day to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[d_val]
    
    # Format start and end times as HH:MM
    start_hour = start_val // 60
    start_minute = start_val % 60
    start_time = f"{start_hour:02d}:{start_minute:02d}"
    
    end_hour = end_val // 60
    end_minute = end_val % 60
    end_time = f"{end_hour:02d}:{end_minute:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()
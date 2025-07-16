from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (540 minutes)
    end_time = Int('end_time')  # in minutes from start_time (duration is 30 minutes)
    
    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)
    
    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)
    
    # Day constraints: Monday (0) or Tuesday (1)
    s.add(day >= 0, day <= 1)
    
    # Jeffrey is free the entire week, so no constraints for Jeffrey
    
    # Harold's constraints
    # Monday (day 0): blocked 9:00-10:00 (540-600), 10:30-17:00 (630-1020)
    # So free on Monday: 10:00-10:30 (600-630)
    # Tuesday (day 1): blocked 9:00-9:30 (540-570), 10:30-11:30 (630-690), 
    #                   12:30-13:30 (750-810), 14:30-15:30 (870-930), 16:00-17:00 (960-1020)
    # So free on Tuesday: 9:30-10:30 (570-630), 11:30-12:30 (690-750), 13:30-14:30 (810-870), 15:30-16:00 (930-960)
    
    # Harold prefers to avoid more meetings on Monday and before 14:30 on Tuesday
    # So we prioritize Tuesday after 14:30 (870 minutes)
    
    # Define free slots
    # Monday free: 10:00-10:30 (600-630)
    monday_free_start = 600
    monday_free_end = 630
    
    # Tuesday free after 14:30: 15:30-16:00 (930-960)
    tuesday_free_start = 930
    tuesday_free_end = 960
    
    # Add constraints for Harold's schedule
    s.add(Or(
        And(day == 0, start_time >= monday_free_start, end_time <= monday_free_end),
        And(day == 1, start_time >= tuesday_free_start, end_time <= tuesday_free_end)
    ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = m[end_time].as_long()
        
        # Convert day to string
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        # Convert start and end times to HH:MM format
        start_hh = start_val // 60
        start_mm = start_val % 60
        end_hh = end_val // 60
        end_mm = end_val % 60
        
        # Format times with leading zeros
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()
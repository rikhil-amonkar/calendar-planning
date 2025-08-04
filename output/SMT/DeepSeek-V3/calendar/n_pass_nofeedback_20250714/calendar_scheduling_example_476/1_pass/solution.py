from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the possible start times in minutes from 9:00 (540 minutes) to 16:30 (990 minutes)
    # Each slot is 30 minutes, so possible start times are 540, 570, ..., 960 (since 16:30 + 30 = 17:00)
    start_time = Int('start_time')
    
    # Constraints: start_time must be within 9:00 (540) to 16:30 (990), in 30-minute increments
    s.add(start_time >= 540)
    s.add(start_time <= 960)  # 16:30 is 990 - 30 = 960 (since meeting is 30 mins)
    s.add(start_time % 30 == 0)  # Ensures start_time is on the half-hour
    
    # Roger's preference: meeting starts at or after 12:30 (750 minutes)
    s.add(start_time >= 750)
    
    # Define the busy intervals for each participant in minutes since midnight
    # Each participant's busy times are converted to minutes for easier comparison
    
    # Kathleen: 14:30 to 15:30 → 870 to 930
    s.add(Or(start_time + 30 <= 870, start_time >= 930))
    
    # Carolyn: 12:00-12:30 (720-750), 13:00-13:30 (780-810)
    s.add(Or(start_time + 30 <= 720, start_time >= 750))
    s.add(Or(start_time + 30 <= 780, start_time >= 810))
    
    # Cheryl: 9:00-9:30 (540-570), 10:00-11:30 (600-690), 12:30-13:30 (750-810), 14:00-17:00 (840-1020)
    s.add(Or(start_time + 30 <= 540, start_time >= 570))
    s.add(Or(start_time + 30 <= 600, start_time >= 690))
    s.add(Or(start_time + 30 <= 750, start_time >= 810))
    s.add(Or(start_time + 30 <= 840, start_time >= 1020))
    
    # Virginia: 9:30-11:30 (570-690), 12:00-12:30 (720-750), 13:00-13:30 (780-810), 14:30-15:30 (870-930), 16:00-17:00 (960-1020)
    s.add(Or(start_time + 30 <= 570, start_time >= 690))
    s.add(Or(start_time + 30 <= 720, start_time >= 750))
    s.add(Or(start_time + 30 <= 780, start_time >= 810))
    s.add(Or(start_time + 30 <= 870, start_time >= 930))
    s.add(Or(start_time + 30 <= 960, start_time >= 1020))
    
    # Angela: 9:30-10:00 (570-600), 10:30-11:30 (630-690), 12:00-12:30 (720-750), 13:00-13:30 (780-810), 14:00-16:30 (840-990)
    s.add(Or(start_time + 30 <= 570, start_time >= 600))
    s.add(Or(start_time + 30 <= 630, start_time >= 690))
    s.add(Or(start_time + 30 <= 720, start_time >= 750))
    s.add(Or(start_time + 30 <= 780, start_time >= 810))
    s.add(Or(start_time + 30 <= 840, start_time >= 990))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + 30
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()
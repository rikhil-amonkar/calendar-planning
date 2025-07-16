from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 00:00 (9:00 is 540, 17:00 is 1020)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Constraints: start time must be between 9:00 (540) and 17:00 (1020) - duration
    s.add(start_time >= 540)
    s.add(end_time <= 1020)
    
    # Define each participant's busy slots in minutes from 00:00
    # Emily: 10:00-10:30 (600-630), 16:00-16:30 (960-990)
    s.add(Or(end_time <= 600, start_time >= 630))
    s.add(Or(end_time <= 960, start_time >= 990))
    
    # Mason is free all day, no constraints
    
    # Maria: 10:30-11:00 (630-660), 14:00-14:30 (840-870)
    s.add(Or(end_time <= 630, start_time >= 660))
    s.add(Or(end_time <= 840, start_time >= 870))
    
    # Carl: 9:30-10:00 (570-600), 10:30-12:30 (630-750), 13:30-14:00 (810-840), 14:30-15:30 (870-930), 16:00-17:00 (960-1020)
    s.add(Or(end_time <= 570, start_time >= 600))
    s.add(Or(end_time <= 630, start_time >= 750))
    s.add(Or(end_time <= 810, start_time >= 840))
    s.add(Or(end_time <= 870, start_time >= 930))
    s.add(Or(end_time <= 960, start_time >= 1020))
    
    # David: 9:30-11:00 (570-660), 11:30-12:00 (690-720), 12:30-13:30 (750-810), 14:00-15:00 (840-900), 16:00-17:00 (960-1020)
    s.add(Or(end_time <= 570, start_time >= 660))
    s.add(Or(end_time <= 690, start_time >= 720))
    s.add(Or(end_time <= 750, start_time >= 810))
    s.add(Or(end_time <= 840, start_time >= 900))
    s.add(Or(end_time <= 960, start_time >= 1020))
    
    # Frank: 9:30-10:30 (570-630), 11:00-11:30 (660-690), 12:30-13:30 (750-810), 14:30-17:00 (870-1020)
    s.add(Or(end_time <= 570, start_time >= 630))
    s.add(Or(end_time <= 660, start_time >= 690))
    s.add(Or(end_time <= 750, start_time >= 810))
    s.add(Or(end_time <= 870, start_time >= 1020))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        # Convert start time from minutes to HH:MM format
        hours = start // 60
        minutes = start % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        end = start + duration
        end_hours = end // 60
        end_minutes = end % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()
from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)  # Not before 9:00
    s.add(end_time <= 1020)    # Not after 17:00
    
    # Anna's preference: not before 14:30 (870 minutes)
    s.add(start_time >= 870)
    
    # Define each participant's busy times in minutes from 9:00
    # Adam: 14:00-15:00 (840-900)
    s.add(Or(end_time <= 840, start_time >= 900))
    
    # John: 13:00-13:30 (780-810), 14:00-14:30 (840-870), 15:30-16:00 (930-960), 16:30-17:00 (990-1020)
    s.add(Or(end_time <= 780, start_time >= 810))
    s.add(Or(end_time <= 840, start_time >= 870))
    s.add(Or(end_time <= 930, start_time >= 960))
    s.add(Or(end_time <= 990, start_time >= 1020))
    
    # Stephanie: 9:30-10:00 (570-600), 10:30-11:00 (630-660), 11:30-16:00 (690-960), 16:30-17:00 (990-1020)
    s.add(Or(end_time <= 570, start_time >= 600))
    s.add(Or(end_time <= 630, start_time >= 660))
    s.add(Or(end_time <= 690, start_time >= 960))
    s.add(Or(end_time <= 990, start_time >= 1020))
    
    # Anna: 9:30-10:00 (570-600), 12:00-12:30 (720-750), 13:00-15:30 (780-930), 16:30-17:00 (990-1020)
    # Note: Anna's preference is already handled with start_time >= 870
    s.add(Or(end_time <= 570, start_time >= 600))
    s.add(Or(end_time <= 720, start_time >= 750))
    s.add(Or(end_time <= 780, start_time >= 930))
    s.add(Or(end_time <= 990, start_time >= 1020))
    
    # Check if there's a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        hours_end = end_min // 60
        minutes_end = end_min % 60
        end_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()
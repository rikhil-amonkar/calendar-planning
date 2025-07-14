from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes from 00:00)
    start_time = Int('start_time')
    
    # Constraint: start time must be within work hours and the meeting must end by 17:00
    s.add(start_time >= work_start)
    s.add(start_time + duration <= work_end)
    
    # Juan's constraints:
    # Busy 9:00-10:30 (540-630), 15:30-16:00 (930-960)
    # Cannot meet after 16:00 (960), so meeting must end by 16:00
    s.add(Or(
        start_time + duration <= 540,  # before 9:00
        start_time >= 630              # after 10:30
    ))
    s.add(Or(
        start_time + duration <= 930,  # before 15:30
        start_time >= 960              # after 16:00
    ))
    s.add(start_time + duration <= 960)  # meeting ends by 16:00 for Juan
    
    # Marilyn's constraints:
    # Busy 11:00-11:30 (660-690), 12:30-13:00 (750-780)
    s.add(Or(
        start_time + duration <= 660,  # before 11:00
        start_time >= 690              # after 11:30
    ))
    s.add(Or(
        start_time + duration <= 750,  # before 12:30
        start_time >= 780              # after 13:00
    ))
    
    # Ronald's constraints:
    # Busy 9:00-10:30 (540-630), 12:00-12:30 (720-750), 13:00-13:30 (780-810), 14:00-16:30 (840-990)
    s.add(Or(
        start_time + duration <= 540,  # before 9:00
        start_time >= 630              # after 10:30
    ))
    s.add(Or(
        start_time + duration <= 720,  # before 12:00
        start_time >= 750              # after 12:30
    ))
    s.add(Or(
        start_time + duration <= 780,  # before 13:00
        start_time >= 810              # after 13:30
    ))
    s.add(Or(
        start_time + duration <= 840,  # before 14:00
        start_time >= 990              # after 16:30
    ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert start_min to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

find_meeting_time()
from z3 import *

def schedule_meeting():
    # Define the variables for the meeting start time (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Work hours are from 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30  # minutes
    
    # Initialize the solver
    s = Solver()
    
    # Constraint: Meeting must start within work hours and end by 17:00
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Judy is free the entire day, so no constraints for Judy
    
    # Nicole's existing meetings:
    # 9:00-10:00 (9*60 to 10*60)
    # 10:30-16:30 (10*60 + 30 to 16*60 + 30)
    # Nicole prefers not to meet before 16:00 (16*60)
    
    # Constraint: Meeting must not overlap with Nicole's existing meetings
    # The meeting cannot overlap with 9:00-10:00 or 10:30-16:30
    s.add(Or(
        And(start_time + meeting_duration <= 10 * 60),  # Ends before 10:00
        And(start_time >= 16 * 60 + 30)                 # Starts after 16:30
    ))
    
    # Additionally, Nicole prefers not to meet before 16:00, so we prioritize after 16:00
    # Since the only feasible slot after 16:00 is 16:30-17:00, we enforce that
    s.add(start_time >= 16 * 60 + 30)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

# Run the function
schedule_meeting()
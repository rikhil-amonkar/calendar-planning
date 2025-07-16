from z3 import *

def find_meeting_time():
    # Create a solver instance
    s = Solver()
    
    # Define the start time variable in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    
    # Meeting duration is 60 minutes (1 hour)
    duration = 60
    end_time = start_time + duration
    
    # Working hours are 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)
    
    # Ryan's busy times: 9:00-9:30 (540-570), 12:30-13:00 (750-780)
    # The meeting cannot overlap with these intervals
    s.add(Or(
        end_time <= 540,  # Meeting ends before Ryan's first busy period starts
        start_time >= 570  # Meeting starts after Ryan's first busy period ends
    ))
    s.add(Or(
        end_time <= 750,  # Meeting ends before Ryan's second busy period starts
        start_time >= 780  # Meeting starts after Ryan's second busy period ends
    ))
    
    # Ruth has no meetings, so no constraints for her
    
    # Denise's busy times: 9:30-10:30 (570-630), 12:00-13:00 (720-780), 14:30-16:30 (870-990)
    # Also, Denise doesn't want to meet after 12:30 (750), so the meeting must end by 12:30
    s.add(end_time <= 750)
    
    # The meeting cannot overlap with Denise's busy times
    s.add(Or(
        end_time <= 570,  # Meeting ends before Denise's first busy period starts
        start_time >= 630  # Meeting starts after Denise's first busy period ends
    ))
    s.add(Or(
        end_time <= 720,  # Meeting ends before Denise's second busy period starts
        start_time >= 780  # Meeting starts after Denise's second busy period ends
    ))
    s.add(Or(
        end_time <= 870,  # Meeting ends before Denise's third busy period starts
        start_time >= 990  # Meeting starts after Denise's third busy period ends
    ))
    
    # Check if there's a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        hours = end_min // 60
        minutes = end_min % 60
        end_str = f"{hours:02d}:{minutes:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

find_meeting_time()
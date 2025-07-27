from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total available time: 9:00 to 17:00 is 8 hours = 480 minutes
    min_time = 0  # 9:00 is 0 minutes from 9:00
    max_time = 480 - duration  # 16:30 is the latest possible start time (16:30 + 30 mins = 17:00)
    
    # Constraint: start_time must be within the work hours
    s.add(start_time >= min_time)
    s.add(start_time <= max_time)
    
    # Define each participant's busy slots in minutes from 9:00
    # Each slot is (start, end) in minutes from 9:00
    patrick = [(13*60 + 30 - 540, 14*60 - 540), (14*60 + 30 - 540, 15*60 - 540)]
    shirley = [(9*60 - 540, 9*60 + 30 - 540), (11*60 - 540, 11*60 + 30 - 540), 
               (12*60 - 540, 12*60 + 30 - 540), (14*60 + 30 - 540, 15*60 - 540), 
               (16*60 - 540, 17*60 - 540)]
    jeffrey = [(9*60 - 540, 9*60 + 30 - 540), (10*60 + 30 - 540, 11*60 - 540), 
               (11*60 + 30 - 540, 12*60 - 540), (13*60 - 540, 13*60 + 30 - 540), 
               (16*60 - 540, 17*60 - 540)]
    gloria = [(11*60 + 30 - 540, 12*60 - 540), (15*60 - 540, 15*60 + 30 - 540)]
    nathan = [(9*60 - 540, 9*60 + 30 - 540), (10*60 + 30 - 540, 12*60 - 540), 
              (14*60 - 540, 17*60 - 540)]
    angela = [(9*60 - 540, 9*60 + 30 - 540), (10*60 - 540, 11*60 - 540), 
              (12*60 + 30 - 540, 15*60 - 540), (15*60 + 30 - 540, 16*60 + 30 - 540)]
    david = [(9*60 - 540, 9*60 + 30 - 540), (10*60 - 540, 10*60 + 30 - 540), 
             (11*60 - 540, 14*60 - 540), (14*60 + 30 - 540, 16*60 + 30 - 540)]
    
    participants = [patrick, shirley, jeffrey, gloria, nathan, angela, david]
    
    # For each participant, add constraints that the meeting does not overlap with any of their busy slots
    for participant in participants:
        for slot in participant:
            slot_start, slot_end = slot
            # The meeting does not overlap with the slot if it's before or after
            s.add(Or(
                start_time + duration <= slot_start,
                start_time >= slot_end
            ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert start_minutes back to HH:MM format
        total_minutes = 540 + start_minutes  # 9:00 is 540 minutes in 24-hour format
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = total_minutes + duration
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
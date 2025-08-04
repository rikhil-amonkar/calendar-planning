from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    
    # Working hours are 9:00 (540) to 17:00 (1020), meeting duration is 30 minutes
    # So start_time must be >= 540 and <= 1020 - 30 = 990
    s.add(start_time >= 540)
    s.add(start_time <= 990)
    
    # Duration is 30 minutes
    meeting_end = start_time + 30
    
    # Margaret's blocked times (in minutes from 0:00)
    margaret_blocked = [
        (540, 600),   # 9:00-10:00
        (630, 660),   # 10:30-11:00
        (690, 720),   # 11:30-12:00
        (780, 810),   # 13:00-13:30
        (900, 930)    # 15:00-15:30
    ]
    
    # Donna's blocked times
    donna_blocked = [
        (870, 900),   # 14:30-15:00
        (960, 990)    # 16:00-16:30
    ]
    
    # Helen's blocked times and preferences
    helen_blocked = [
        (540, 570),   # 9:00-9:30
        (600, 690),    # 10:00-11:30
        (780, 840),    # 13:00-14:00
        (870, 900),    # 14:30-15:00
        (930, 1020)    # 15:30-17:00
    ]
    # Helen doesn't want to meet after 13:30 (810 minutes)
    s.add(meeting_end <= 810)
    
    # Function to add no-overlap constraints
    def add_no_overlap(blocked_periods):
        for (block_start, block_end) in blocked_periods:
            s.add(Or(
                meeting_end <= block_start,
                start_time >= block_end
            ))
    
    # Add constraints for each participant
    add_no_overlap(margaret_blocked)
    add_no_overlap(donna_blocked)
    add_no_overlap(helen_blocked)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + 30
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()
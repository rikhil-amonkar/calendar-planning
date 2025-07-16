from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()
    
    # Define the possible start times in minutes from 9:00 (540 minutes) to 16:30 (990 minutes)
    # The meeting is 30 minutes, so the latest start time is 16:30 (which ends at 17:00)
    start_time = Int('start_time')
    s.add(start_time >= 540)   # 9:00 in minutes (9 * 60)
    s.add(start_time <= 990)   # 16:30 in minutes (16 * 60 + 30)
    # Ensure the start time is in 30-minute increments (0 or 30 minutes past the hour)
    s.add(start_time % 30 == 0)
    
    # Meeting duration is 30 minutes
    end_time = start_time + 30
    
    # Each participant's busy times in minutes since midnight
    # Gregory: 9:00-9:30 (540-570), 11:30-12:00 (690-720)
    s.add(Not(And(start_time < 570, end_time > 540)))  # overlaps with 9:00-9:30
    s.add(Not(And(start_time < 720, end_time > 690)))  # overlaps with 11:30-12:00
    
    # Jonathan: 9:00-9:30 (540-570), 12:00-12:30 (720-750), 13:00-13:30 (780-810), 15:00-16:00 (900-960), 16:30-17:00 (990-1020)
    s.add(Not(And(start_time < 570, end_time > 540)))  # 9:00-9:30
    s.add(Not(And(start_time < 750, end_time > 720)))  # 12:00-12:30
    s.add(Not(And(start_time < 810, end_time > 780)))  # 13:00-13:30
    s.add(Not(And(start_time < 960, end_time > 900)))  # 15:00-16:00
    s.add(Not(And(start_time < 1020, end_time > 990))) # 16:30-17:00
    
    # Barbara: 10:00-10:30 (600-630), 13:30-14:00 (810-840)
    s.add(Not(And(start_time < 630, end_time > 600)))  # 10:00-10:30
    s.add(Not(And(start_time < 840, end_time > 810)))  # 13:30-14:00
    
    # Jesse: 10:00-11:00 (600-660), 12:30-14:30 (750-870)
    s.add(Not(And(start_time < 660, end_time > 600)))  # 10:00-11:00
    s.add(Not(And(start_time < 870, end_time > 750)))  # 12:30-14:30
    
    # Alan: 9:30-11:00 (570-660), 11:30-12:30 (690-750), 13:00-15:30 (780-930), 16:00-17:00 (960-1020)
    s.add(Not(And(start_time < 660, end_time > 570)))  # 9:30-11:00
    s.add(Not(And(start_time < 750, end_time > 690)))  # 11:30-12:30
    s.add(Not(And(start_time < 930, end_time > 780)))  # 13:00-15:30
    s.add(Not(And(start_time < 1020, end_time > 960))) # 16:00-17:00
    
    # Nicole: 9:00-10:30 (540-630), 11:30-12:00 (690-720), 12:30-13:30 (750-810), 14:00-17:00 (840-1020)
    s.add(Not(And(start_time < 630, end_time > 540)))  # 9:00-10:30
    s.add(Not(And(start_time < 720, end_time > 690)))  # 11:30-12:00
    s.add(Not(And(start_time < 810, end_time > 750)))  # 12:30-13:30
    s.add(Not(And(start_time < 1020, end_time > 840))) # 14:00-17:00
    
    # Catherine: 9:00-10:30 (540-630), 12:00-13:30 (720-810), 15:00-15:30 (900-930), 16:00-16:30 (960-990)
    s.add(Not(And(start_time < 630, end_time > 540)))  # 9:00-10:30
    s.add(Not(And(start_time < 810, end_time > 720)))  # 12:00-13:30
    s.add(Not(And(start_time < 930, end_time > 900)))  # 15:00-15:30
    s.add(Not(And(start_time < 990, end_time > 960)))  # 16:00-16:30
    
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

find_meeting_time()
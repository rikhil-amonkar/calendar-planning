from z3 import *

def find_meeting_time():
    # Initialize solver
    s = Solver()
    
    # Define the start time variable in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)  # 9:00
    s.add(end_time <= 1020)   # 17:00
    
    # Define each participant's blocked time slots in minutes from midnight
    # Doris's blocked times: 9:00-11:00 (540-660), 13:30-14:00 (810-840), 16:00-16:30 (960-990)
    s.add(Or(
        end_time <= 540,  # before 9:00
        start_time >= 660,  # after 11:00
        And(end_time <= 810, start_time >= 660),  # between 11:00 and 13:30
        And(end_time <= 960, start_time >= 840),  # between 14:00 and 16:00
        start_time >= 990   # after 16:30
    ))
    
    # Theresa's blocked times: 10:00-12:00 (600-720)
    s.add(Or(
        end_time <= 600,
        start_time >= 720
    ))
    
    # Christian has no meetings, no constraints
    
    # Terry's blocked times: 9:30-10:00 (570-600), 11:30-12:00 (690-720), 12:30-13:00 (750-780), 
    # 13:30-14:00 (810-840), 14:30-15:00 (870-900), 15:30-17:00 (930-1020)
    s.add(Or(
        end_time <= 570,
        And(start_time >= 600, end_time <= 690),
        And(start_time >= 720, end_time <= 750),
        And(start_time >= 780, end_time <= 810),
        And(start_time >= 840, end_time <= 870),
        And(start_time >= 900, end_time <= 930),
        start_time >= 1020
    ))
    
    # Carolyn's blocked times: 9:00-10:30 (540-630), 11:00-11:30 (660-690), 12:00-13:00 (720-780),
    # 13:30-14:30 (810-870), 15:00-17:00 (900-1020)
    s.add(Or(
        end_time <= 540,
        And(start_time >= 630, end_time <= 660),
        And(start_time >= 690, end_time <= 720),
        And(start_time >= 780, end_time <= 810),
        And(start_time >= 870, end_time <= 900),
        start_time >= 1020
    ))
    
    # Kyle's blocked times: 9:00-9:30 (540-570), 11:30-12:00 (690-720), 12:30-13:00 (750-780),
    # 14:30-17:00 (870-1020)
    s.add(Or(
        end_time <= 540,
        And(start_time >= 570, end_time <= 690),
        And(start_time >= 720, end_time <= 750),
        And(start_time >= 780, end_time <= 870),
        start_time >= 1020
    ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        hours_end = end_min // 60
        minutes_end = end_min % 60
        end_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

find_meeting_time()
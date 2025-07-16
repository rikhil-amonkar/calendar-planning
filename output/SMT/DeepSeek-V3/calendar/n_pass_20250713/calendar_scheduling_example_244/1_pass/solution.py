from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total available time is from 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)
    s.add(start_time + duration <= 1020)
    
    # Define each participant's busy slots in minutes from midnight
    # Walter is free all day
    # No constraints for Walter
    
    # Cynthia's busy slots: 9:00-9:30, 10:00-10:30, 13:30-14:30, 15:00-16:00
    # Convert to minutes: 540-570, 600-630, 810-870, 900-960
    s.add(Or(
        start_time + duration <= 540,  # meeting ends before 9:00
        start_time >= 570              # meeting starts after 9:30
    ))
    s.add(Or(
        start_time + duration <= 600,
        start_time >= 630
    ))
    s.add(Or(
        start_time + duration <= 810,
        start_time >= 870
    ))
    s.add(Or(
        start_time + duration <= 900,
        start_time >= 960
    ))
    
    # Ann's busy slots: 10:00-11:00, 13:00-13:30, 14:00-15:00, 16:00-16:30
    # Convert to minutes: 600-660, 780-810, 840-900, 960-990
    s.add(Or(
        start_time + duration <= 600,
        start_time >= 660
    ))
    s.add(Or(
        start_time + duration <= 780,
        start_time >= 810
    ))
    s.add(Or(
        start_time + duration <= 840,
        start_time >= 900
    ))
    s.add(Or(
        start_time + duration <= 960,
        start_time >= 990
    ))
    
    # Catherine's busy slots: 9:00-11:30, 12:30-13:30, 14:30-17:00
    # Convert to minutes: 540-690, 750-810, 870-1020
    s.add(Or(
        start_time + duration <= 540,
        start_time >= 690
    ))
    s.add(Or(
        start_time + duration <= 750,
        start_time >= 810
    ))
    s.add(Or(
        start_time + duration <= 870,
        start_time >= 1020
    ))
    
    # Kyle's busy slots: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-14:30, 15:00-16:00
    # Convert to minutes: 540-570, 600-690, 720-750, 780-870, 900-960
    s.add(Or(
        start_time + duration <= 540,
        start_time >= 570
    ))
    s.add(Or(
        start_time + duration <= 600,
        start_time >= 690
    ))
    s.add(Or(
        start_time + duration <= 720,
        start_time >= 750
    ))
    s.add(Or(
        start_time + duration <= 780,
        start_time >= 870
    ))
    s.add(Or(
        start_time + duration <= 900,
        start_time >= 960
    ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert start_min back to HH:MM
        hours = start_min // 60
        minutes = start_min % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

find_meeting_time()
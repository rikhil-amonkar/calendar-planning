from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 (0 mins) to 17:00 (480 mins)
    work_start = 0
    work_end = 480  # 8 hours * 60 minutes
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraints for the meeting to be within work hours
    s.add(start >= work_start)
    s.add(start + duration <= work_end)
    
    # Juan's constraints:
    # Busy: 9:00-10:30 (0-90), 15:30-16:00 (390-420)
    # Can't meet after 16:00 (420 mins)
    s.add(Or(
        And(start >= 90, start + duration <= 390),  # 10:30-15:30
        And(start >= 420, start + duration <= 480)   # 16:00-17:00 (but Juan can't meet after 16:00)
    ))
    # So effectively only 10:30-15:30 is available for Juan
    
    # Marilyn's constraints:
    # Busy: 11:00-11:30 (120-150), 12:30-13:00 (210-240)
    s.add(Or(
        start + duration <= 120,  # Before 11:00
        And(start >= 150, start + duration <= 210),  # 11:30-12:30
        start >= 240              # After 13:00
    ))
    
    # Ronald's constraints:
    # Busy: 9:00-10:30 (0-90), 12:00-12:30 (180-210), 13:00-13:30 (240-270), 14:00-16:30 (300-450)
    s.add(Or(
        And(start >= 90, start + duration <= 180),  # 10:30-12:00
        And(start >= 210, start + duration <= 240),  # 12:30-13:00
        And(start >= 270, start + duration <= 300),  # 13:30-14:00
        start >= 450                                # After 16:30
    ))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_time = model[start].as_long()
        
        # Convert start_time back to HH:MM format
        hours = 9 + start_time // 60
        minutes = start_time % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_time = start_time + duration
        end_hours = 9 + end_time // 60
        end_minutes = end_time % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()
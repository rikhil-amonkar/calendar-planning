from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 (which is 0 minutes)
    work_start = 0  # 9:00 is 0 minutes
    work_end = 8 * 60  # 17:00 is 480 minutes (8 hours after 9:00)
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    
    # Define the start time variable (in minutes since 9:00)
    start = Int('start')
    
    # Constraints for the meeting to be within work hours
    s.add(start >= work_start)
    s.add(start + duration <= work_end)
    
    # Busy times for each participant (each is a list of (start, end) in minutes since 9:00)
    anthony_busy = [
        (30, 60),    # 9:30-10:00
        (180, 240),   # 12:00-13:00
        (420, 450)    # 16:00-16:30
    ]
    
    pamela_busy = [
        (30, 60),     # 9:30-10:00
        (450, 480)    # 16:30-17:00
    ]
    
    zachary_busy = [
        (0, 150),     # 9:00-11:30
        (180, 210),   # 12:00-12:30
        (240, 270),   # 13:00-13:30
        (330, 360),   # 14:30-15:00
        (420, 480)    # 16:00-17:00
    ]
    
    # Function to add no-overlap constraints for a participant's busy times
    def add_no_overlap_constraints(busy_times):
        for (busy_start, busy_end) in busy_times:
            s.add(Or(
                start + duration <= busy_start,
                start >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(anthony_busy)
    add_no_overlap_constraints(pamela_busy)
    add_no_overlap_constraints(zachary_busy)
    
    # Pamela's preference: meeting must end by 14:30 (330 minutes from 9:00)
    s.add(start + duration <= 330)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Convert start_min back to HH:MM format
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()
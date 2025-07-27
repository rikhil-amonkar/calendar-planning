from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()
    
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Variables for meeting start and end times (in minutes since midnight)
    start = Int('start')
    end = Int('end')
    
    # Constraints for work hours and duration
    s.add(start >= work_start)
    s.add(end <= work_end)
    s.add(end == start + duration)
    
    # Michael's busy slots (in minutes since midnight)
    michael_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (15 * 60, 15 * 60 + 30),      # 15:00-15:30
        (16 * 60, 16 * 60 + 30)       # 16:00-16:30
    ]
    
    # Arthur's busy slots
    arthur_busy = [
        (9 * 60, 12 * 60),            # 9:00-12:00
        (13 * 60, 15 * 60),           # 13:00-15:00
        (15 * 60 + 30, 16 * 60),      # 15:30-16:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    
    # Eric's calendar is open, no constraints
    
    # Add constraints for Michael's busy times
    for (busy_start, busy_end) in michael_busy:
        s.add(Or(end <= busy_start, start >= busy_end))
    
    # Add constraints for Arthur's busy times
    for (busy_start, busy_end) in arthur_busy:
        s.add(Or(end <= busy_start, start >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_min = model.eval(start).as_long()
        end_min = model.eval(end).as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_hh = end_min // 60
        end_mm = end_min % 60
        
        # Format the output
        solution = (
            f"SOLUTION:\n"
            f"Day: Monday\n"
            f"Start Time: {start_hh:02d}:{start_mm:02d}\n"
            f"End Time: {end_hh:02d}:{end_mm:02d}"
        )
        print(solution)
    else:
        print("No solution found.")

find_meeting_time()
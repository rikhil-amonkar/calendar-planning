from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Define the start time in minutes since 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Working hours: 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540)  # 9:00
    s.add(end_time <= 1020)   # 17:00
    
    # Define each participant's busy slots in minutes since midnight
    # Bradley's busy slots:
    bradley_busy = [
        (570, 600),    # 9:30-10:00
        (750, 780),    # 12:30-13:00
        (810, 840),    # 13:30-14:00
        (930, 960)     # 15:30-16:00
    ]
    
    # Teresa's busy slots:
    teresa_busy = [
        (630, 660),    # 10:30-11:00
        (720, 750),    # 12:00-12:30
        (780, 810),    # 13:00-13:30
        (870, 900)      # 14:30-15:00
    ]
    
    # Elizabeth's busy slots:
    elizabeth_busy = [
        (540, 570),     # 9:00-9:30
        (630, 690),     # 10:30-11:30
        (780, 810),     # 13:00-13:30
        (870, 900),     # 14:30-15:00
        (930, 1020)     # 15:30-17:00
    ]
    
    # Christian's busy slots:
    christian_busy = [
        (540, 570),     # 9:00-9:30
        (630, 1020)      # 10:30-17:00
    ]
    
    # Function to add constraints that the meeting does not overlap with any busy slot
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            # The meeting must be either entirely before or entirely after the busy slot
            s.add(Or(end_time <= busy_start, start_time >= busy_end))
    
    # Add constraints for each participant
    add_no_overlap_constraints(bradley_busy)
    add_no_overlap_constraints(teresa_busy)
    add_no_overlap_constraints(elizabeth_busy)
    add_no_overlap_constraints(christian_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        end_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()
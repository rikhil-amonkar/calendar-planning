from z3 import *

def solve_meeting_scheduling():
    # Create a solver instance
    s = Solver()
    
    # Define the start time as an integer representing minutes from 9:00 (540 minutes since midnight)
    start_time = Int('start_time')
    
    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Constraint: start_time must be within work hours and the meeting must end by 17:00
    s.add(start_time >= work_start)
    s.add(start_time + duration <= work_end)
    
    # Emily's busy times (in minutes since midnight)
    emily_busy = [
        (600, 630),    # 10:00-10:30
        (690, 750),    # 11:30-12:30
        (840, 900),     # 14:00-15:00
        (960, 990)      # 16:00-16:30
    ]
    
    # Melissa's busy times
    melissa_busy = [
        (570, 600),    # 9:30-10:00
        (870, 900)      # 14:30-15:00
    ]
    
    # Frank's busy times
    frank_busy = [
        (600, 630),     # 10:00-10:30
        (660, 690),     # 11:00-11:30
        (750, 780),     # 12:30-13:00
        (810, 870),     # 13:30-14:30
        (900, 960),     # 15:00-16:00
        (990, 1020)     # 16:30-17:00
    ]
    
    # Frank's preference: does not want to meet after 9:30 (i.e., start_time must be <= 570 (9:30))
    s.add(start_time <= 570)
    
    # Function to add no-overlap constraints for a person's busy times
    def add_no_overlap_constraints(busy_times):
        for (busy_start, busy_end) in busy_times:
            # The meeting must not overlap with any busy interval
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(emily_busy)
    add_no_overlap_constraints(melissa_busy)
    add_no_overlap_constraints(frank_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_meeting_scheduling()
from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 = 9:00, 60 = 10:00, etc.)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480 - duration  # Latest start time is 16:30 (450 minutes from 9:00)
    
    # Constraint: start_time must be between 0 and max_time inclusive
    s.add(start_time >= 0)
    s.add(start_time <= max_time)
    
    # Define each participant's busy intervals in minutes from 9:00
    # Each interval is (start, end) in minutes
    # Cynthia's busy intervals
    cynthia_busy = [
        (30, 90),   # 9:30-10:30
        (150, 180),  # 11:30-12:00
        (240, 270),  # 13:00-13:30
        (360, 420)   # 15:00-16:00
    ]
    
    # Lauren's busy intervals
    lauren_busy = [
        (0, 30),     # 9:00-9:30
        (90, 120),   # 10:30-11:00
        (150, 180),  # 11:30-12:00
        (240, 270),  # 13:00-13:30
        (300, 330),  # 14:00-14:30
        (360, 390),  # 15:00-15:30
        (420, 480)   # 16:00-17:00
    ]
    
    # Robert's busy intervals
    robert_busy = [
        (90, 120),   # 10:30-11:00
        (150, 180),  # 11:30-12:00
        (210, 270),  # 12:30-13:30
        (300, 420)    # 14:00-16:00
    ]
    
    # Steven and Roy are free all day, so no constraints
    
    # Function to add constraints that the meeting does not overlap with any busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must be entirely before the busy interval or entirely after
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant's busy intervals
    add_no_overlap_constraints(cynthia_busy)
    add_no_overlap_constraints(lauren_busy)
    add_no_overlap_constraints(robert_busy)
    
    # Check for the earliest possible start time
    # To find the earliest, we can check if there's a solution and then find the minimal start_time
    if s.check() == sat:
        m = s.model()
        earliest_start = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        start_hour = 9 + earliest_start // 60
        start_minute = earliest_start % 60
        end_time = earliest_start + duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()
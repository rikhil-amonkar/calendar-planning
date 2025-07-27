from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 represents 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480
    
    # Constraint: start_time must be >= 0 and <= max_time - duration
    s.add(start_time >= 0)
    s.add(start_time <= max_time - duration)
    
    # Define the busy intervals for each participant in minutes from 9:00
    # Gregory's busy intervals
    gregory_busy = [
        (0, 60),      # 9:00-10:00
        (90, 150),     # 10:30-11:30
        (210, 240),    # 12:30-13:00
        (270, 300)     # 13:30-14:00
    ]
    
    # Natalie has no busy intervals
    
    # Christine's busy intervals
    christine_busy = [
        (0, 150),      # 9:00-11:30
        (270, 480)      # 13:30-17:00
    ]
    
    # Vincent's busy intervals
    vincent_busy = [
        (0, 30),        # 9:00-9:30
        (90, 180),      # 10:30-12:00
        (210, 300),     # 12:30-14:00
        (330, 480)      # 14:30-17:00
    ]
    
    # Function to add constraints that the meeting does not overlap with any busy interval
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting should not overlap with this interval: so either meeting ends before busy_start or starts after busy_end
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant's busy intervals
    add_no_overlap_constraints(gregory_busy)
    add_no_overlap_constraints(christine_busy)
    add_no_overlap_constraints(vincent_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert start_min back to HH:MM format
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()
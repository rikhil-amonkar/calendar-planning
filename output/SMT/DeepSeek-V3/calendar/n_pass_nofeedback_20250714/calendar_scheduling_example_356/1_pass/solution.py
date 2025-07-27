from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 is 9:00, 60 is 10:00, etc.)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    min_time = 0
    max_time = 480 - duration  # The latest start time is 16:30 (450 minutes)
    
    # Constraint: start_time must be within working hours
    s.add(start_time >= min_time)
    s.add(start_time <= max_time)
    
    # Define each person's busy intervals in minutes from 9:00
    # Katherine: 12:00-12:30 (180-210), 13:00-14:30 (240-330)
    katherine_busy = [(180, 210), (240, 330)]
    
    # Rebecca: no meetings
    rebecca_busy = []
    
    # Julie: 9:00-9:30 (0-30), 10:30-11:00 (90-120), 13:30-14:00 (270-300), 15:00-15:30 (360-390)
    julie_busy = [(0, 30), (90, 120), (270, 300), (360, 390)]
    
    # Angela: 9:00-10:00 (0-60), 10:30-11:00 (90-120), 11:30-14:00 (150-300), 14:30-15:00 (330-360), 16:30-17:00 (450-480)
    angela_busy = [(0, 60), (90, 120), (150, 300), (330, 360), (450, 480)]
    
    # Nicholas: 9:30-11:00 (30-120), 11:30-13:30 (150-270), 14:00-16:00 (300-420), 16:30-17:00 (450-480)
    nicholas_busy = [(30, 120), (150, 270), (300, 420), (450, 480)]
    
    # Carl: 9:00-11:00 (0-120), 11:30-12:30 (150-210), 13:00-14:30 (240-330), 15:00-16:00 (360-420), 16:30-17:00 (450-480)
    carl_busy = [(0, 120), (150, 210), (240, 330), (360, 420), (450, 480)]
    
    # Function to add constraints that the meeting does not overlap with busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(katherine_busy)
    add_no_overlap_constraints(rebecca_busy)
    add_no_overlap_constraints(julie_busy)
    add_no_overlap_constraints(angela_busy)
    add_no_overlap_constraints(nicholas_busy)
    add_no_overlap_constraints(carl_busy)
    
    # Angela's preference: meeting after 15:00 (360 minutes from 9:00)
    s.add(start_time >= 360)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert start_min back to HH:MM format
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()
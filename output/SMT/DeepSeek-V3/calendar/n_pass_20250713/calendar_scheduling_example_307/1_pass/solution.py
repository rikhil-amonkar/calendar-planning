from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the possible start times (in minutes from 9:00)
    start_time = Int('start_time')
    s.add(start_time >= 0)  # 9:00 is 0 minutes
    s.add(start_time <= 480 - 30)  # 17:00 is 480 minutes (8 hours * 60), minus 30 minutes
    
    # Convert each participant's busy times to constraints
    # Each busy time is a tuple (start, end) in minutes from 9:00
    busy_times = [
        # Stephen's busy times: 10:00-10:30, 12:00-12:30
        (60, 90), (180, 210),
        # Brittany's busy times: 11:00-11:30, 13:30-14:00, 15:30-16:00, 16:30-17:00
        (120, 150), (270, 300), (390, 420), (450, 480),
        # Dorothy's busy times: 9:00-9:30, 10:00-10:30, 11:00-12:30, 13:00-15:00, 15:30-17:00
        (0, 30), (60, 90), (120, 210), (240, 360), (390, 480),
        # Rebecca's busy times: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-17:00
        (30, 90), (120, 150), (180, 210), (240, 480),
        # Jordan's busy times: 9:00-9:30, 10:00-11:00, 11:30-12:00, 13:00-15:00, 15:30-16:30
        (0, 30), (60, 120), (150, 180), (240, 360), (390, 450)
    ]
    
    # Add constraints that the meeting does not overlap with any busy time
    for busy_start, busy_end in busy_times:
        s.add(Or(
            start_time + 30 <= busy_start,
            start_time >= busy_end
        ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = 9 + start_min // 60
        start_mm = start_min % 60
        end_min = start_min + 30
        end_hh = 9 + end_min // 60
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
        print("No solution found")

solve_scheduling()
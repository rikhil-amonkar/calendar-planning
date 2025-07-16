from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    solver = Solver()
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes from midnight)
    start_time = Int('start_time')
    
    # Constraints for the start time within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + duration <= work_end)
    
    # Christine's meetings (in minutes from midnight)
    christine_meetings = [
        (660, 690),    # 11:00-11:30
        (900, 930)     # 15:00-15:30
    ]
    
    # Helen's meetings and blocked times (in minutes from midnight)
    helen_meetings = [
        (570, 630),    # 9:30-10:30
        (660, 690),    # 11:00-11:30
        (720, 750),     # 12:00-12:30
        (810, 960),     # 13:30-16:00
        (990, 1020)     # 16:30-17:00
    ]
    
    # Helen cannot meet after 15:00, so meeting must end by 15:00 (900 minutes)
    solver.add(start_time + duration <= 900)
    
    # Add constraints for not overlapping with Christine's meetings
    for (s, e) in christine_meetings:
        solver.add(Or(start_time >= e, start_time + duration <= s))
    
    # Add constraints for not overlapping with Helen's meetings
    for (s, e) in helen_meetings:
        solver.add(Or(start_time >= e, start_time + duration <= s))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert start minutes to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_min = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_min:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling_problem()
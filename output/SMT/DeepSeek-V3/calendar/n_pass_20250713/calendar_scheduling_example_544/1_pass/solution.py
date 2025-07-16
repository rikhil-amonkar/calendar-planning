from z3 import *

def schedule_meeting():
    # Initialize the solver
    solver = Solver()
    
    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Albert's busy slots in minutes since midnight
    albert_busy = [
        (9 * 60, 10 * 60),       # 9:00 to 10:00
        (10 * 60 + 30, 12 * 60),  # 10:30 to 12:00
        (15 * 60, 16 * 60 + 30)   # 15:00 to 16:30
    ]
    
    # Albert cannot meet after 11:00 (so meeting must end by 11:00)
    albert_no_meet_after = 11 * 60
    
    # Deborah is free all day, so no constraints except work hours
    
    # The meeting start time variable (in minutes since midnight)
    start_time = Int('start_time')
    
    # Constraints:
    # 1. Meeting must start within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)
    
    # 2. Meeting must not overlap with Albert's busy slots
    for busy_start, busy_end in albert_busy:
        solver.add(Or(
            start_time + meeting_duration <= busy_start,
            start_time >= busy_end
        ))
    
    # 3. Meeting must end by 11:00 (Albert's constraint)
    solver.add(start_time + meeting_duration <= albert_no_meet_after)
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start // 60
        start_mm = start % 60
        end = start + meeting_duration
        end_hh = end // 60
        end_mm = end % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

# Run the function
schedule_meeting()
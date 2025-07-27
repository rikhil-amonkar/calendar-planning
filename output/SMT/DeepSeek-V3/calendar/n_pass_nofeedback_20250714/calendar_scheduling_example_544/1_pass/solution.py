from z3 import *

def find_meeting_time():
    # Initialize the solver
    solver = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes since 00:00)
    start_time = Int('start_time')
    
    # Albert's constraints:
    # Albert's blocked times in minutes since 00:00:
    # 9:00-10:00 (540-600), 10:30-12:00 (630-720), 15:00-16:30 (900-990)
    # Also, Albert cannot meet after 11:00 (660 minutes)
    
    # The meeting must end by 11:00 (start_time + duration <= 660)
    # So end time is start_time + duration ≤ 11:00 (660 minutes)
    
    # Constraints:
    # 1. Meeting must start within work hours (start_time >= 540 and start_time + duration <= 1020)
    solver.add(start_time >= work_start)
    solver.add(start_time + duration <= work_end)
    
    # 2. Meeting must end by 11:00 (660 minutes)
    solver.add(start_time + duration <= 11 * 60)
    
    # 3. The meeting should not overlap with Albert's blocked times
    # Albert's blocked intervals:
    blocked_intervals = [
        (9 * 60, 10 * 60),      # 9:00-10:00
        (10 * 60 + 30, 12 * 60), # 10:30-12:00
        (15 * 60, 16 * 60 + 30)  # 15:00-16:30
    ]
    
    for (block_start, block_end) in blocked_intervals:
        # The meeting is outside the blocked interval: 
        # meeting ends before block starts OR starts after block ends
        solver.add(Or(
            start_time + duration <= block_start,
            start_time >= block_end
        ))
    
    # Deborah is free all day, so no constraints from her
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        # Prepare the solution output
        solution = f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
        return solution
    else:
        return "No solution found."

# Execute the function and print the result
print(find_meeting_time())
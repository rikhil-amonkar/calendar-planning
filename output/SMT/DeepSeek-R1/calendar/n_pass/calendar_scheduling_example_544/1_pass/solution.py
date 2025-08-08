from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time variable in minutes
    start = Int('start')
    
    # Convert time to minutes
    work_start = 9 * 60  # 9:00 -> 540 minutes
    albert_end = 11 * 60 # 11:00 -> 660 minutes
    
    # Meeting duration in minutes
    duration = 30
    
    # Albert's blocked intervals in minutes: [start, end)
    blocked_intervals = [
        (9 * 60, 10 * 60),    # 9:00-10:00 (540-600)
        (10 * 60 + 30, 12 * 60) # 10:30-12:00 (630-720)
    ]
    
    # Constraints:
    # 1. Meeting must start within work hours (at or after 9:00)
    s.add(start >= work_start)
    # 2. Meeting must end by 11:00 due to Albert's constraint
    s.add(start + duration <= albert_end)
    
    # 3. Meeting must not overlap with any of Albert's blocked intervals
    for (block_start, block_end) in blocked_intervals:
        # The meeting must either end before the blocked interval starts or start after the blocked interval ends
        s.add(Or(
            start + duration <= block_start,
            start >= block_end
        ))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start].as_long()
        
        # Convert start_min back to HH:MM format
        hour = start_min // 60
        minute = start_min % 60
        start_time = f"{hour:02d}:{minute:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        end_hour = end_min // 60
        end_minute = end_min % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()
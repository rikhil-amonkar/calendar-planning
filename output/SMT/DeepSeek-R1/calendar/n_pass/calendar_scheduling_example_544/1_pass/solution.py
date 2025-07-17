from z3 import *

def main():
    # Reference: 9:00 is 0 minutes
    work_start_min = 0
    work_end_min = 8 * 60  # 17:00 is 480 minutes from 9:00
    duration = 30  # Meeting duration in minutes
    
    # Albert cannot meet after 11:00, which is 120 minutes from 9:00
    albert_deadline = 2 * 60  # 120 minutes
    
    # Blocked times represented as half-open intervals [start, end)
    blocked_intervals = [
        (0, 60),    # 9:00-10:00
        (90, 180),  # 10:30-12:00
        (360, 450)  # 15:00-16:30
    ]
    
    # Initialize Z3 solver and variable
    s = Solver()
    start_time_min = Int('start_time_min')
    
    # Constraints
    # Meeting must start within work hours and end by 17:00
    s.add(start_time_min >= work_start_min)
    s.add(start_time_min <= work_end_min - duration)
    
    # Meeting must end by 11:00 (Albert's constraint)
    s.add(start_time_min + duration <= albert_deadline)
    
    # Meeting must not overlap any blocked interval
    for (b_start, b_end) in blocked_intervals:
        s.add(Or(start_time_min + duration <= b_start, start_time_min >= b_end))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_min_val = model[start_time_min].as_long()
        
        # Convert start time back to HH:MM format
        total_min = 9 * 60 + start_min_val
        hours = total_min // 60
        minutes = total_min % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_min_val = start_min_val + duration
        total_end_min = 9 * 60 + end_min_val
        hours_end = total_end_min // 60
        minutes_end = total_end_min % 60
        end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
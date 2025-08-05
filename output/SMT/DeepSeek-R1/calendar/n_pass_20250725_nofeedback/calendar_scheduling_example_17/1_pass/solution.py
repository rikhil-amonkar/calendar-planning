from z3 import *

def main():
    # Create a solver instance
    s = Solver()
    
    # Define the start time variable in minutes from 9:00
    start = Int('start')
    
    # Meeting duration is 30 minutes
    duration = 30
    end = start + duration
    
    # Constraints: start must be between 0 (9:00) and 240 (13:00) because end must be <= 270 (13:30)
    s.add(start >= 0)
    s.add(end <= 270)  # meeting must end by 13:30
    
    # Busy intervals for each participant (start, end) in minutes from 9:00, only those starting before 270
    busy_intervals = [
        # Margaret's busy intervals
        (0, 60),
        (90, 120),
        (150, 180),
        (240, 270),
        # Helen's busy intervals
        (0, 30),
        (60, 150),
        (240, 300)
    ]
    
    # Donna has no busy intervals before 270 minutes
    
    # Add constraints for each busy interval: meeting must not overlap
    for (b_start, b_end) in busy_intervals:
        s.add(Or(end <= b_start, start >= b_end))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Convert minutes back to time in HH:MM format
        total_minutes = start_min
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        hours_end = 9 + end_min // 60
        minutes_end = end_min % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
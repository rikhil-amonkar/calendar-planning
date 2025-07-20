from z3 import *

def main():
    # Initialize Z3 solver
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start = Int('start')
    duration = 30  # Meeting duration in minutes
    
    # Work hours: 9:00 (0 minutes) to 17:00 (480 minutes)
    work_start = 0
    work_end = 480
    
    # Evelyn's constraint: meeting must end by 13:00 (240 minutes from 9:00)
    evelyn_end = 240
    
    # Randy's blocked time intervals (half-open: [start, end))
    blocks = [
        (0, 90),    # 9:00 to 10:30
        (120, 390), # 11:00 to 15:30
        (420, 480)  # 16:00 to 17:00
    ]
    
    # Add constraints
    s.add(start >= work_start)  # Meeting starts at or after 9:00
    s.add(start + duration <= work_end)  # Meeting ends by 17:00
    s.add(start + duration <= evelyn_end)  # Meeting ends by 13:00 for Evelyn
    
    # Add constraints to avoid Randy's blocked times
    for (a, b) in blocks:
        s.add(Or(start + duration <= a, start >= b))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Convert start time to HH:MM
        total_minutes = start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{9 + end_hours}:{end_minutes:02d}"
        
        # Print the solution
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
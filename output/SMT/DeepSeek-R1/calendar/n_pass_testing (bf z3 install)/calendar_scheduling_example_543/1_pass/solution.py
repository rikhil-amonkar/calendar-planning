from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraints: start must be between 0 and 420 (inclusive)
    s.add(start >= 0)
    s.add(start <= 420)  # because 420 + 60 = 480 (17:00)
    
    # James' busy times (in minutes from 9:00)
    james_busy = [(150, 180), (330, 360)]
    
    # John's busy times (in minutes from 9:00)
    john_busy = [(30, 120), (150, 180), (210, 270), (330, 450)]
    
    # For James: meeting must not overlap with any of his busy intervals
    for (busy_start, busy_end) in james_busy:
        s.add(Or(start + 60 <= busy_start, start >= busy_end))
    
    # For John: meeting must not overlap with any of his busy intervals
    for (busy_start, busy_end) in john_busy:
        s.add(Or(start + 60 <= busy_start, start >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start].as_long()
        
        # Convert start_min to time string
        hours = start_min // 60
        minutes = start_min % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        # Calculate end time
        end_min = start_min + 60
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_time = f"{9 + end_hours}:{end_minutes:02d}"
        
        print(f"Monday, {start_time}, {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
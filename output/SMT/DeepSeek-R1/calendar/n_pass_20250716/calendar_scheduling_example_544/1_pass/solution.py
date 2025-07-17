from z3 import *

def main():
    # Define the start time variable in minutes (from 00:00, so 9:00 is 540)
    s = Int('s')
    
    # Constraints for the meeting
    constraints = [
        s >= 540,             # Meeting must start at or after 9:00
        s + 30 <= 660,         # Meeting must end by 11:00 (660 minutes)
        
        # Albert's blocked intervals (as half-open: [start, end))
        # Block 1: 9:00 to 10:00 [540, 600)
        Or(s + 30 <= 540, s >= 600),
        
        # Block 2: 10:30 to 12:00 [630, 720)
        Or(s + 30 <= 630, s >= 720),
        
        # Block 3: 15:00 to 16:30 [900, 990) - not needed because meeting ends by 11:00
    ]
    
    # Create solver and add constraints
    solver = Solver()
    solver.add(constraints)
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        start_min = m[s].as_long()
        # Calculate end time
        end_min = start_min + 30
        # Convert to hours and minutes
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_hour = end_min // 60
        end_minute = end_min % 60
        # Format the time strings
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        # Output the solution
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
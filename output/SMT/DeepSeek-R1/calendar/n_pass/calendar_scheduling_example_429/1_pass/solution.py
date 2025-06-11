from z3 import *

def main():
    # Initialize the solver and the start time variable
    s = Int('s')
    solver = Solver()
    
    # Constraints: meeting must start between 0 and 450 minutes (9:00 to 16:30)
    solver.add(s >= 0)
    solver.add(s <= 450)
    
    # Busy intervals for each participant in minutes relative to 9:00
    judy = [(240, 270), (420, 450)]
    olivia = [(60, 90), (180, 240), (300, 330)]
    jacqueline = [(60, 90), (360, 390)]
    laura = [(0, 60), (90, 180), (240, 270), (330, 360), (390, 480)]
    tyler = [(0, 60), (120, 150), (210, 240), (300, 330), (390, 480)]
    lisa = [(30, 90), (120, 150), (180, 210), (240, 270), (300, 330), (420, 480)]
    
    # Add constraints for each participant's busy intervals
    for intervals in [judy, olivia, jacqueline, laura, tyler, lisa]:
        for (a, b) in intervals:
            solver.add(Or(s + 30 <= a, s >= b))
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[s].as_long()
        
        # Convert start time to HH:MM format
        total_minutes = 9 * 60 + start_minutes
        hour = total_minutes // 60
        minute = total_minutes % 60
        start_time = f"{hour:02d}:{minute:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        total_end_minutes = 9 * 60 + end_minutes
        end_hour = total_end_minutes // 60
        end_minute = total_end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the meeting details
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
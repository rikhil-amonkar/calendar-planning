from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define time in minutes from 9:00 (0) to 17:00 (480)
    start = Int('start')
    meeting_duration = 30
    
    # Constraints: meeting must be within 9:00-17:00
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)
    
    # Lisa's busy intervals (in minutes from 9:00)
    lisa_busy = [(0, 30), (90, 120), (300, 420)]
    # Anthony's busy intervals
    anthony_busy = [(0, 30), (120, 150), (210, 270), (300, 360), (390, 420), (450, 480)]
    
    # Add constraints for Lisa
    for (busy_start, busy_end) in lisa_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Add constraints for Anthony
    for (busy_start, busy_end) in anthony_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Check for earliest solution
    if s.check() == sat:
        m = s.model()
        best_start = m.evaluate(start).as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + best_start // 60
        start_minute = best_start % 60
        end_time = best_start + meeting_duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
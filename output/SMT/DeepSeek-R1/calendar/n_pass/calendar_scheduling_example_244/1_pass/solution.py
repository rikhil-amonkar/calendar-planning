from z3 import *

def main():
    # Initialize solver and variable
    S = Int('S')
    s = Solver()
    
    # Meeting duration in minutes
    duration = 30
    # Total available time: 9:00 (0 min) to 17:00 (480 min)
    s.add(S >= 0)
    s.add(S <= 480 - duration)  # Meeting must end by 17:00
    
    # Busy intervals for each participant (in minutes from 9:00)
    # Format: [ (start1, end1), (start2, end2), ... ]
    busy_intervals = {
        'Cynthia': [(0, 30), (60, 90), (270, 330), (360, 420)],
        'Ann': [(60, 120), (240, 270), (300, 360), (420, 450)],
        'Catherine': [(0, 150), (210, 270), (330, 480)],
        'Kyle': [(0, 30), (60, 150), (180, 210), (240, 330), (360, 420)]
    }
    
    # Add constraints for each busy interval of every participant
    for intervals in busy_intervals.values():
        for (B, E) in intervals:
            # Ensure no overlap: meeting must end before the busy interval starts or start after it ends
            s.add(Or(S + duration <= B, S >= E))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[S].as_long()
        
        # Calculate start time in hours and minutes
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the time strings
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        
        # Output the result
        print("Monday")
        print(start_str)
        print(end_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
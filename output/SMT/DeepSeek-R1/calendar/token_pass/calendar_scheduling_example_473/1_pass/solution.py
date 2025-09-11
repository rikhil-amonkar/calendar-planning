from z3 import *

def main():
    # Initialize solver
    s = Solver()
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 30
    
    # Total available time window in minutes (9:00 to 17:00)
    total_minutes = 480
    s.add(start >= 0)
    s.add(start <= total_minutes - duration)
    
    # Define busy intervals for each participant in minutes from 9:00
    busy_times = {
        "Gregory": [(0, 30), (150, 180)],
        "Jonathan": [(0, 30), (180, 210), (240, 270), (360, 420), (450, 480)],
        "Barbara": [(60, 90), (270, 300)],
        "Jesse": [(60, 120), (210, 330)],
        "Alan": [(30, 120), (150, 210), (240, 390), (420, 480)],
        "Nicole": [(0, 90), (150, 180), (210, 270), (300, 480)],
        "Catherine": [(0, 90), (180, 270), (360, 390), (420, 450)]
    }
    
    # Add constraints for each participant
    for person, intervals in busy_times.items():
        for (busy_start, busy_end) in intervals:
            # Meeting must not overlap with any busy interval
            s.add(Or(start + duration <= busy_start, start >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m.evaluate(start).as_long()
        
        # Convert start and end times to HH:MM format
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        # Format the output
        print(f"Monday: {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
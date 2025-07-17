from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Work day: 9:00 (0 minutes) to 17:00 (480 minutes)
    start = Int('start')
    meeting_duration = 30
    
    # Start time must be within [0, 450] to fit the meeting before 17:00
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Michael's busy intervals (in minutes)
    michael_busy = [(30, 90), (360, 390), (420, 450)]
    # For each busy interval, ensure the meeting doesn't overlap
    for (busy_start, busy_end) in michael_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Arthur's busy intervals (in minutes)
    arthur_busy = [(0, 180), (240, 360), (390, 420), (450, 480)]
    for (busy_start, busy_end) in arthur_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + meeting_duration
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the meeting time
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    total_minutes = 480
    max_start = total_minutes - meeting_duration
    
    # Start time variable (in minutes from 9:00)
    S = Int('S')
    s.add(S >= 0, S <= max_start)
    
    # Convert busy intervals to minutes from 9:00
    busy_intervals = {
        'Gregory': [(0, 60), (90, 150), (210, 240), (270, 300)],
        'Christine': [(0, 150), (270, 480)],
        'Vincent': [(0, 30), (90, 180), (210, 300), (330, 480)]
    }
    
    # Natalie has no busy intervals
    
    # Add constraints for each participant's busy intervals
    for person, intervals in busy_intervals.items():
        for start_busy, end_busy in intervals:
            # Meeting must not overlap with busy interval
            s.add(Or(S + meeting_duration <= start_busy, end_busy <= S))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(S).as_long()
        
        # Convert start minutes to time string
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
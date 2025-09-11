from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Total available time in minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    max_start = total_minutes - meeting_duration
    
    # Start time variable (in minutes from 9:00)
    S = Int('S')
    s.add(S >= 0, S <= max_start)
    
    # Define busy intervals for each participant in minutes from 9:00
    busy_times = {
        'Doris': [(0, 120), (270, 300), (420, 450)],
        'Theresa': [(60, 180)],
        'Christian': [],
        'Terry': [(30, 60), (150, 180), (210, 240), (270, 300), (330, 360), (390, 480)],
        'Carolyn': [(0, 90), (120, 150), (180, 240), (270, 330), (360, 480)],
        'Kyle': [(0, 30), (150, 180), (210, 240), (330, 480)]
    }
    
    # Add constraints: Meeting must not overlap with any busy interval
    for person, intervals in busy_times.items():
        for start_busy, end_busy in intervals:
            s.add(Or(S + meeting_duration <= start_busy, S >= end_busy))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.eval(S).as_long()
        
        # Calculate start and end times
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
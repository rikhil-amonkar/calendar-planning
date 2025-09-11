from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Time representation in minutes from 9:00 (0 minutes = 9:00)
    start_time = Int('start_time')
    meeting_duration = 30
    total_minutes = 8 * 60  # 9:00 to 17:00 is 8 hours
    
    # Constraint: meeting must start between 9:00 and (17:00 - duration)
    s.add(start_time >= 0)
    s.add(start_time <= total_minutes - meeting_duration)
    
    # Busy intervals in minutes from 9:00
    busy_intervals = {
        'Megan': [(0, 30), (60, 120), (180, 210)],
        'Christine': [(0, 30), (150, 180), (240, 300), (390, 450)],
        'Gabriel': [],
        'Sara': [(150, 180), (330, 360)],
        'Bruce': [(30, 60), (90, 180), (210, 300), (330, 360), (390, 450)],
        'Kathryn': [(60, 330), (420, 450)],
        'Billy': [(0, 30), (120, 150), (180, 300), (330, 390)]
    }
    
    # For each participant, ensure meeting doesn't overlap with any busy interval
    for person, intervals in busy_intervals.items():
        for start_busy, end_busy in intervals:
            # Meeting must be entirely before or after the busy interval
            s.add(Or(
                start_time + meeting_duration <= start_busy,
                start_time >= end_busy
            ))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert start minutes to time string
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define time in minutes from 9:00 (0 minutes = 9:00)
    start_time = Int('start_time')
    meeting_duration = 30
    total_minutes = 480  # 9:00 to 17:00 is 8 hours = 480 minutes
    
    # Constraints: start_time must be between 0 and 450 (to allow 30-minute meeting before 17:00)
    s.add(start_time >= 0)
    s.add(start_time <= total_minutes - meeting_duration)
    
    # Define busy intervals in minutes from 9:00
    busy_times = [
        # Judy
        [(13*60 - 9*60, 13*60 + 30 - 9*60), (16*60 - 9*60, 16*60 + 30 - 9*60)],
        # Olivia
        [(10*60 - 9*60, 10*60 + 30 - 9*60), (12*60 - 9*60, 13*60 - 9*60), (14*60 - 9*60, 14*60 + 30 - 9*60)],
        # Eric - no busy times
        [],
        # Jacqueline
        [(10*60 - 9*60, 10*60 + 30 - 9*60), (15*60 - 9*60, 15*60 + 30 - 9*60)],
        # Laura
        [(0, 60), (10*60 + 30 - 9*60, 12*60 - 9*60), (13*60 - 9*60, 13*60 + 30 - 9*60), (14*60 + 30 - 9*60, 15*60 - 9*60), (15*60 + 30 - 9*60, total_minutes)],
        # Tyler
        [(0, 60), (11*60 - 9*60, 11*60 + 30 - 9*60), (12*60 + 30 - 9*60, 13*60 - 9*60), (14*60 - 9*60, 14*60 + 30 - 9*60), (15*60 + 30 - 9*60, total_minutes)],
        # Lisa
        [(9*60 + 30 - 9*60, 10*60 + 30 - 9*60), (11*60 - 9*60, 11*60 + 30 - 9*60), (12*60 - 9*60, 12*60 + 30 - 9*60), (13*60 - 9*60, 13*60 + 30 - 9*60), (14*60 - 9*60, 14*60 + 30 - 9*60), (16*60 - 9*60, total_minutes)]
    ]
    
    # For each person, add constraints that the meeting doesn't overlap with their busy times
    for person_busy in busy_times:
        for busy_start, busy_end in person_busy:
            # Meeting must not overlap: it must end before busy start or start after busy end
            s.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start_time).as_long()
        
        # Convert start_minutes to time format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
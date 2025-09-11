from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 minutes = 9:00)
    start_minutes = Int('start_minutes')
    meeting_duration = 30
    total_minutes_in_work_day = 8 * 60  # 9:00 to 17:00 is 8 hours
    
    # Constraint: Meeting must start between 9:00 (0) and 16:30 (450 minutes) to fit within 17:00
    s.add(start_minutes >= 0)
    s.add(start_minutes <= total_minutes_in_work_day - meeting_duration)
    
    # Define busy intervals in minutes relative to 9:00
    ashley_busy = [(60, 90), (120, 180), (210, 240), (360, 420)]
    ronald_busy = [(0, 30), (60, 150), (210, 300), (330, 480)]
    larry_busy = [(0, 180), (240, 480)]
    
    # For each participant, add constraints that the meeting does not overlap with any busy interval
    # Meeting: [start_minutes, start_minutes + meeting_duration]
    for busy in ashley_busy:
        s.add(Or(
            start_minutes + meeting_duration <= busy[0],
            start_minutes >= busy[1]
        ))
    
    for busy in ronald_busy:
        s.add(Or(
            start_minutes + meeting_duration <= busy[0],
            start_minutes >= busy[1]
        ))
    
    for busy in larry_busy:
        s.add(Or(
            start_minutes + meeting_duration <= busy[0],
            start_minutes >= busy[1]
        ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m.evaluate(start_minutes).as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_minutes = start_val + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()
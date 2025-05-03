from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # One-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Stephanie's constraints
    # Busy during 9:00-9:30 (0-30) and 13:30-14:00 (270-300)
    s.add(Or(start + meeting_duration <= 0, start >= 30))
    s.add(Or(start + meeting_duration <= 270, start >= 300))
    
    # Mark's preference (avoid before 15:00 → start >= 360)
    s.add(start >= 360)
    
    # Scott's constraints
    # Busy during 9:00-10:00 (0-60), 11:00-12:30 (120-210), 14:30-15:00 (330-360), 16:00-17:00 (420-480)
    s.add(Or(start + meeting_duration <= 0, start >= 60))
    s.add(Or(start + meeting_duration <= 120, start >= 210))
    s.add(Or(start + meeting_duration <= 330, start >= 360))
    s.add(Or(start + meeting_duration <= 420, start >= 480))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
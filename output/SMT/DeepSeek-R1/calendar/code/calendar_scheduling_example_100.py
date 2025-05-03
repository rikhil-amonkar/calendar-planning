from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # One-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Henry's constraints
    # Busy during 9:00-9:30 (0-30), 10:00-10:30 (60-90), 12:00-14:30 (180-330), 15:00-16:00 (360-420), 16:30-17:00 (450-480)
    s.add(Or(start + meeting_duration <= 0, start >= 30))
    s.add(Or(start + meeting_duration <= 60, start >= 90))
    s.add(Or(start + meeting_duration <= 180, start >= 330))
    s.add(Or(start + meeting_duration <= 360, start >= 420))
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Christian's constraints
    # Busy during 9:00-11:00 (0-120), 14:30-15:30 (330-390), 16:00-17:00 (420-480)
    s.add(Or(start + meeting_duration <= 0, start >= 120))
    s.add(Or(start + meeting_duration <= 330, start >= 390))
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
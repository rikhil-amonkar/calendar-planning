from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Madison's constraints
    # Busy during 10:00-10:30 (60-90), 14:30-15:00 (330-360), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    s.add(Or(start + meeting_duration <= 60, start >= 90))
    s.add(Or(start + meeting_duration <= 330, start >= 360))
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Logan's constraints
    # Busy during 9:00-12:00 (0-180), 12:30-16:00 (210-420), 16:30-17:00 (450-480)
    s.add(start >= 180)  # Must start after first block
    s.add(Or(start + meeting_duration <= 210, start >= 420))  # Avoid second block
    s.add(Or(start + meeting_duration <= 450, start >= 480))  # Avoid third block
    
    # Virginia's constraints
    # Busy during 9:30-11:00 (30-120), 11:30-12:00 (90-180), 13:00-14:30 (240-330), 15:00-15:30 (360-390), 16:00-17:00 (420-480)
    s.add(Or(start + meeting_duration <= 30, start >= 120))
    s.add(Or(start + meeting_duration <= 90, start >= 180))
    s.add(Or(start + meeting_duration <= 240, start >= 330))
    s.add(Or(start + meeting_duration <= 360, start >= 390))
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
from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # One-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Joseph's constraints
    # Can't meet before 14:30 (330 minutes)
    s.add(start >= 330)
    # Busy periods: 9:00-10:00 (0-60), 10:30-11:00 (90-120), 12:30-13:00 (210-240), 14:30-15:30 (330-390)
    s.add(Or(start + meeting_duration <= 0, start >= 60))
    s.add(Or(start + meeting_duration <= 90, start >= 120))
    s.add(Or(start + meeting_duration <= 210, start >= 240))
    s.add(Or(start + meeting_duration <= 330, start >= 390))
    
    # Kyle's constraints
    # Busy during 12:30-13:30 (210-270)
    s.add(Or(start + meeting_duration <= 210, start >= 270))
    
    # Joan's constraints
    # Busy during 9:00-9:30 (0-30), 10:00-10:30 (60-90), 11:00-11:30 (120-150), 12:30-14:00 (210-300),
    # 14:30-15:00 (330-360), 15:30-16:00 (390-420)
    s.add(Or(start + meeting_duration <= 0, start >= 30))
    s.add(Or(start + meeting_duration <= 60, start >= 90))
    s.add(Or(start + meeting_duration <= 120, start >= 150))
    s.add(Or(start + meeting_duration <= 210, start >= 300))
    s.add(Or(start + meeting_duration <= 330, start >= 360))
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
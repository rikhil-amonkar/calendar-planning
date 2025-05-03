from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (9:00 = 0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Kelly has no constraints
    
    # Julia's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 14:00-14:30 → 300-330 minutes
    s.add(Or(start + meeting_duration <= 300, start >= 330))
    # 15:00-15:30 → 360-390 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    # 16:30-17:00 → 450-480 minutes
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    # Julia's preference: meeting ends by 13:30 (270 minutes)
    s.add(start + meeting_duration <= 270)
    
    # Martha's constraints
    # 9:00-11:00 → 0-120 minutes
    s.add(Or(start + meeting_duration <= 0, start >= 120))
    # 12:00-15:00 → 180-360 minutes
    s.add(Or(start + meeting_duration <= 180, start >= 360))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
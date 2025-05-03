from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Anthony's constraints
    # 14:00-14:30 → 300-330 minutes
    s.add(Or(start + meeting_duration <= 300, start >= 330))
    # 15:00-15:30 → 360-390 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    
    # Ronald's constraints
    # 9:00-10:00 → 0-60 minutes
    s.add(Or(start + meeting_duration <= 0, start >= 60))
    # 12:00-12:30 → 180-210 minutes
    s.add(Or(start + meeting_duration <= 180, start >= 210))
    # 13:30-14:00 → 270-300 minutes
    s.add(Or(start + meeting_duration <= 270, start >= 300))
    
    # Jonathan's constraints
    # 9:00-10:00 → 0-60 minutes
    s.add(Or(start + meeting_duration <= 0, start >= 60))
    # 11:00-11:30 → 120-150 minutes
    s.add(Or(start + meeting_duration <= 120, start >= 150))
    # 12:00-13:00 → 180-240 minutes
    s.add(Or(start + meeting_duration <= 180, start >= 240))
    # 14:00-14:30 → 300-330 minutes
    s.add(Or(start + meeting_duration <= 300, start >= 330))
    # 15:00-17:00 → 360-480 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 480))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
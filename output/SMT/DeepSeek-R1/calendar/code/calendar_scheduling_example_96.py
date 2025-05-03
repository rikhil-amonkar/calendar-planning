from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Christopher's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 10:30-11:00 → 90-120 minutes
    s.add(Or(start + meeting_duration <= 90, start >= 120))
    # 11:30-13:00 → 150-240 minutes
    s.add(Or(start + meeting_duration <= 150, start >= 240))
    # 15:00-15:30 → 360-390 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    
    # Robert's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 11:00-11:30 → 120-150 minutes
    s.add(Or(start + meeting_duration <= 120, start >= 150))
    # 12:00-12:30 → 180-210 minutes
    s.add(Or(start + meeting_duration <= 180, start >= 210))
    # 13:30-14:30 → 270-330 minutes
    s.add(Or(start + meeting_duration <= 270, start >= 330))
    # 15:00-15:30 → 360-390 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    
    # Wayne's constraints
    # Busy during 10:00-17:00 → 60-480 minutes
    s.add(start + meeting_duration <= 60)
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
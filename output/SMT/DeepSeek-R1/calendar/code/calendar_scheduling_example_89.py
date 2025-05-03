from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Michelle's constraints
    # 11:00-12:00 → 120-180 minutes
    s.add(Or(start + meeting_duration <= 120, start >= 180))
    # 14:00-15:00 → 300-360 minutes
    s.add(Or(start + meeting_duration <= 300, start >= 360))
    
    # Andrea's constraints
    # 9:00-9:30 → 0-30 minutes
    s.add(start >= 30)
    # 11:30-12:30 → 150-210 minutes
    s.add(Or(start + meeting_duration <= 150, start >= 210))
    # 13:30-14:00 → 270-300 minutes
    s.add(Or(start + meeting_duration <= 270, start >= 300))
    # 14:30-15:00 → 330-360 minutes
    s.add(Or(start + meeting_duration <= 330, start >= 360))
    # 16:00-16:30 → 420-450 minutes
    s.add(Or(start + meeting_duration <= 420, start >= 450))
    
    # Douglas's constraints
    # 9:00-9:30 → 0-30 minutes
    s.add(start >= 30)
    # 10:00-10:30 → 60-90 minutes
    s.add(Or(start + meeting_duration <= 60, start >= 90))
    # 11:00-15:00 → 120-360 minutes
    s.add(Or(start + meeting_duration <= 120, start >= 360))
    # 16:00-17:00 → 420-480 minutes
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
from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (9:00 = 0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Michael's constraints
    # 9:30-10:30 → 30-90 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 90))
    # 15:00-15:30 → 360-390 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    # 16:00-16:30 → 420-450 minutes
    s.add(Or(start + meeting_duration <= 420, start >= 450))
    
    # Arthur's constraints
    # 9:00-12:00 → 0-180 minutes
    s.add(Or(start + meeting_duration <= 0, start >= 180))
    # 13:00-15:00 → 240-360 minutes
    s.add(Or(start + meeting_duration <= 240, start >= 360))
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    # 16:30-17:00 → 450-480 minutes
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Eric has no constraints
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
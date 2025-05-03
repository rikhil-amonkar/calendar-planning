from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Brittany's constraints
    # 12:00-13:30 → 180-270 minutes
    s.add(Or(start + meeting_duration <= 180, start >= 270))
    # 14:30-15:00 → 330-360 minutes
    s.add(Or(start + meeting_duration <= 330, start >= 360))
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    # 16:30-17:00 → 450-480 minutes
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Wayne's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 13:00-15:00 → 240-360 minutes
    s.add(Or(start + meeting_duration <= 240, start >= 360))
    # 16:30-17:00 → 450-480 minutes
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Charles's constraints
    # 9:00-9:30 → 0-30 minutes
    s.add(Or(start + meeting_duration <= 0, start >= 30))
    # 10:00-10:30 → 60-90 minutes
    s.add(Or(start + meeting_duration <= 60, start >= 90))
    # 11:30-13:30 → 150-270 minutes
    s.add(Or(start + meeting_duration <= 150, start >= 270))
    # 14:30-16:30 → 330-450 minutes
    s.add(Or(start + meeting_duration <= 330, start >= 450))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
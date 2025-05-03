from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Danielle's constraints
    # 9:00-10:00 → 0-60 minutes
    s.add(start >= 60)
    # 10:30-11:00 → 90-120 minutes
    s.add(start >= 120)
    # 14:30-15:00 → 330-360 minutes
    s.add(Or(start + meeting_duration <= 330, start >= 360))
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    # 16:30-17:00 → 450-480 minutes
    s.add(start + meeting_duration <= 450)
    
    # Bruce's constraints
    # 11:00-11:30 → 120-150 minutes
    s.add(start >= 150)
    # 12:30-13:00 → 210-240 minutes
    s.add(start >= 240)
    # 14:00-14:30 → 300-330 minutes
    s.add(Or(start + meeting_duration <= 300, start >= 330))
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    
    # Eric's constraints
    # 9:00-9:30 → 0-30 minutes
    s.add(start >= 30)
    # 10:00-11:00 → 60-120 minutes
    s.add(start >= 120)
    # 11:30-13:00 → 150-240 minutes
    s.add(start >= 240)
    # 14:30-15:30 → 330-390 minutes
    s.add(Or(start + meeting_duration <= 330, start >= 390))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
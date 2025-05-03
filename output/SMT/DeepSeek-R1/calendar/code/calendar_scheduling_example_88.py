from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Joseph's constraints
    # 9:00-9:30 → 0-30 minutes
    s.add(start >= 30)  # Meeting must start after 9:30
    # 12:30-13:00 → 210-240 minutes
    s.add(Or(start + meeting_duration <= 210, start >= 240))
    
    # Isabella's constraints
    # 9:00-10:30 → 0-90 minutes
    s.add(start >= 90)
    # 11:30-12:00 → 150-180 minutes
    s.add(Or(start + meeting_duration <= 150, start >= 180))
    # 13:30-14:00 → 270-300 minutes
    s.add(Or(start + meeting_duration <= 270, start >= 300))
    # 14:30-17:00 → 330-480 minutes
    s.add(start + meeting_duration <= 330)  # Must end before 14:30
    
    # Dennis has no constraints
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
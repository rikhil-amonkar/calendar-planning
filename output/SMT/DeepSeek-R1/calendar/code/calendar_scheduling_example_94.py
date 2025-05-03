from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Elizabeth's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 11:30-12:00 → 150-180 minutes
    s.add(Or(start + meeting_duration <= 150, start >= 180))
    # 13:30-14:30 → 270-330 minutes
    s.add(Or(start + meeting_duration <= 270, start >= 330))
    # 15:00-15:30 → 360-390 minutes
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    # 16:30-17:00 → 450-480 minutes
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Sandra's constraints
    # Can't meet before 13:00 (240 minutes)
    s.add(start >= 240)
    # Busy during 11:30-13:30 (150-270 minutes)
    s.add(start >= 270)
    # Busy during 15:30-16:30 (390-450 minutes)
    s.add(Or(start + meeting_duration <= 390, start >= 450))
    
    # Nicholas has no constraints
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
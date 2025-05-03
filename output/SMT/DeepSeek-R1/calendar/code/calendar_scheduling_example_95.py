from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Jennifer's constraints
    # Can't meet before 12:30 (210 minutes)
    s.add(start >= 210)
    # Avoid 16:00-16:30 (420-450 minutes)
    s.add(Or(start + meeting_duration <= 420, start >= 450))
    
    # Gary's constraints
    # 9:30-10:00 (30-60 minutes)
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 10:30-11:00 (90-120 minutes)
    s.add(Or(start + meeting_duration <= 90, start >= 120))
    # 11:30-12:30 (150-180 minutes)
    s.add(Or(start + meeting_duration <= 150, start >= 180))
    # 14:00-14:30 (300-330 minutes)
    s.add(Or(start + meeting_duration <= 300, start >= 330))
    # 16:30-17:00 (450-480 minutes)
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Frances's constraints
    # Busy during 9:00-11:00 (0-120), 11:30-12:30 (150-210), 13:00-17:00 (240-480)
    s.add(start >= 120)  # Avoid 0-120 block
    s.add(Or(start + meeting_duration <= 150, start >= 210))  # Avoid 150-210 block
    s.add(start + meeting_duration <= 240)  # Avoid 240-480 block
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
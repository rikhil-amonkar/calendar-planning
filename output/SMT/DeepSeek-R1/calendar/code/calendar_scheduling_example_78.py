from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (9:00 = 0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Ronald's constraints
    # Busy: 9:00-10:00 (0-60), 11:00-12:00 (120-180)
    s.add(start >= 60)  # After 10:00
    s.add(Or(start + meeting_duration <= 120, start >= 180))  # Avoid 120-180
    
    # Teresa's constraints
    # Busy: 10:30-11:00 (90-120), 14:00-14:30 (300-330)
    s.add(Or(start + meeting_duration <= 90, start >= 120))  # Avoid 90-120
    s.add(Or(start + meeting_duration <= 300, start >= 330))  # Avoid 300-330
    
    # Carol's constraints
    # Busy: 9:00-12:30 (0-210), 14:00-15:30 (300-390), 16:00-17:00 (420-480)
    s.add(start >= 210)  # After 12:30
    s.add(start + meeting_duration <= 300)  # End by 14:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
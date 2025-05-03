from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Juan's constraints
    # Can't meet before 10:30 (90 minutes) and must end by 15:30 (390 minutes)
    s.add(start >= 90)
    s.add(start + meeting_duration <= 390)
    
    # Marilyn's constraints
    # Avoid 11:00-11:30 (120-150) and 12:30-13:00 (210-240)
    s.add(Or(start + meeting_duration <= 120, start >= 150))
    s.add(Or(start + meeting_duration <= 210, start >= 240))
    
    # Ronald's constraints
    # Avoid 12:00-12:30 (180-210), 13:00-13:30 (240-270), and 14:00-16:30 (300-450)
    s.add(Or(start + meeting_duration <= 180, start >= 210))
    s.add(Or(start + meeting_duration <= 240, start >= 270))
    s.add(Or(start + meeting_duration <= 300, start >= 450))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
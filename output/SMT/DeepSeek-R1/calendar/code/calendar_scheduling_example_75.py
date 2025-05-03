from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60
    
    # Base constraints for time window (9:00-17:00)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # 17:00 = 480 minutes
    
    # Jacob's constraints
    # Busy: 9:00-9:30 (0-30), 12:30-13:00 (210-240), 14:30-15:00 (330-360), 16:30-17:00 (450-480)
    s.add(start >= 30)  # After 9:30
    s.add(Or(start + 60 <= 210, start >= 240))  # Avoid 12:30-13:00
    s.add(Or(start + 60 <= 330, start >= 360))  # Avoid 14:30-15:00
    s.add(start + 60 <= 450)  # End before 16:30
    
    # Amanda's constraints
    # Busy: 10:00-10:30 (60-90), 12:00-12:30 (180-210)
    s.add(Or(start + 60 <= 60, start >= 90))  # Avoid 10:00-10:30
    s.add(Or(start + 60 <= 180, start >= 210))  # Avoid 12:00-12:30
    
    # Lisa's constraints
    # Busy: 11:00-13:00 (120-240), 14:30-16:30 (330-450)
    s.add(Or(start + 60 <= 120, start >= 240))  # Avoid 11:00-13:00
    s.add(start + 60 <= 330)  # End before 14:30
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
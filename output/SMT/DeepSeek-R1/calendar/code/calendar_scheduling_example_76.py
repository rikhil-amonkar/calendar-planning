from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60
    
    # Base constraints for time window (9:00-17:00 in minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # 17:00 = 480 minutes
    
    # Joyce has no meetings (no additional constraints)
    
    # Beverly's constraints (busy intervals in minutes)
    # 9:30-10:00 (30-60), 11:00-11:30 (120-150), 12:30-13:00 (210-240)
    # 14:00-14:30 (300-330), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    s.add(Or(start + 60 <= 30, start >= 60))      # Avoid 30-60
    s.add(Or(start + 60 <= 120, start >= 150))    # Avoid 120-150
    s.add(Or(start + 60 <= 210, start >= 240))    # Avoid 210-240
    s.add(Or(start + 60 <= 300, start >= 330))    # Avoid 300-330
    s.add(Or(start + 60 <= 390, start >= 420))    # Avoid 390-420
    s.add(Or(start + 60 <= 450, start >= 480))    # Avoid 450-480
    
    # Peter's constraints (busy intervals in minutes)
    # 9:30-10:30 (30-90), 11:30-13:00 (150-240)
    # 14:30-15:30 (330-390), 16:30-17:00 (450-480)
    s.add(Or(start + 60 <= 30, start >= 90))      # Avoid 30-90
    s.add(Or(start + 60 <= 150, start >= 240))    # Avoid 150-240
    s.add(Or(start + 60 <= 330, start >= 390))    # Avoid 330-390
    s.add(Or(start + 60 <= 450, start >= 480))    # Avoid 450-480
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
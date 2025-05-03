from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    
    # Meeting duration and time window constraints
    s.add(start >= 0)
    s.add(start <= 450)  # 450 + 30 = 480 (17:00)
    
    # Bradley's constraints
    s.add(Or(start <= 0, start >= 60))            # Avoid 9:30-10:00 (30-60)
    s.add(Or(start + 30 <= 240, start >= 270))    # Avoid 13:00-13:30 (240-270)
    s.add(Or(start + 30 <= 330, start >= 360))    # Avoid 14:30-15:00 (330-360)
    s.add(start <= 420)                           # Avoid 16:30-17:00 (450-480)
    
    # Andrew's constraints
    s.add(start >= 30)                            # Avoid 9:00-9:30 (0-30)
    s.add(Or(start + 30 <= 210, start >= 270))    # Avoid 12:30-13:30 (210-270)
    s.add(Or(start + 30 <= 300, start >= 330))    # Avoid 14:00-14:30 (300-330)
    s.add(Or(start + 30 <= 360, start >= 420))    # Avoid 15:00-16:00 (360-420)
    
    # Melissa's constraints
    s.add(start >= 30)                            # Avoid 9:00-9:30 (0-30)
    s.add(Or(start + 30 <= 60, start >= 90))      # Avoid 10:00-10:30 (60-90)
    s.add(Or(start + 30 <= 120, start >= 300))    # Avoid 11:00-14:00 (120-300)
    s.add(Or(start + 30 <= 360, start >= 390))    # Avoid 15:00-15:30 (360-390)
    s.add(Or(start + 30 <= 420, start >= 450))    # Avoid 16:00-16:30 (420-450)
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
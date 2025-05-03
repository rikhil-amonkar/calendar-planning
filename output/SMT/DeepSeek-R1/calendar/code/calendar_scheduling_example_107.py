from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Peter's constraints: 0-30 (9:00-9:30), 90-120 (10:30-11:00), 150-180 (11:30-12:00), 210-240 (12:30-13:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 90, start >= 120))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 210, start >= 240))
    
    # Judith has no constraints
    
    # Keith's constraints: 150-180 (11:30-12:00), 210-360 (12:30-15:00), 390-420 (15:30-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 210, start >= 360))
    s.add(Or(start + duration <= 390, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Evelyn's constraints: 0-210 (9:00-12:30), 270-390 (13:30-15:30), 450-480 (16:30-17:00)
    s.add(start >= 210)  # Must start after 12:30
    s.add(Or(start + duration <= 270, start >= 390))  # Avoid 13:30-15:30
    s.add(start + duration <= 450)  # Must end before 16:30
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
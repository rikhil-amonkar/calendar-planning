from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Scott's constraints: 0-30 (9:00-9:30), 90-150 (10:30-11:30), 270-300 (13:30-14:00), 330-390 (14:30-15:30)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 90, start >= 150))
    s.add(Or(start + duration <= 270, start >= 300))
    s.add(Or(start + duration <= 330, start >= 390))
    
    # Laura's constraints: 60-90 (10:00-10:30), 330-360 (14:30-15:00)
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 330, start >= 360))
    
    # Marilyn's constraints: 0-30 (9:00-9:30), 60-360 (10:00-15:00), 390-480 (15:30-17:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 60, start >= 360))
    s.add(Or(start + duration <= 390, start >= 480))
    
    # Natalie's constraints: 0-30 (9:00-9:30), 60-90 (10:00-10:30), 120-180 (11:00-12:00), 210-420 (12:30-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 120, start >= 180))
    s.add(Or(start + duration <= 210, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
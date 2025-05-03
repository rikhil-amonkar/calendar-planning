from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Gregory's constraints: 0-60 (9:00-10:00), 90-150 (10:30-11:30), 210-240 (12:30-13:00), 270-300 (13:30-14:00)
    s.add(Or(start + duration <= 0, start >= 60))
    s.add(Or(start + duration <= 90, start >= 150))
    s.add(Or(start + duration <= 210, start >= 240))
    s.add(Or(start + duration <= 270, start >= 300))
    
    # Christine's constraints: 0-150 (9:00-11:30), 270-480 (13:30-17:00)
    s.add(start >= 150)
    s.add(start + duration <= 270)
    
    # Vincent's constraints: 0-30 (9:00-9:30), 90-180 (10:30-12:00), 210-300 (12:30-14:00), 330-480 (14:30-17:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 90, start >= 180))
    s.add(Or(start + duration <= 210, start >= 300))
    s.add(Or(start + duration <= 330, start >= 480))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
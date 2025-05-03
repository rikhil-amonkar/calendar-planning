from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 60  # One-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Stephanie's constraints: 60-90 (10:00-10:30), 420-450 (16:00-16:30)
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 420, start >= 450))
    
    # Cheryl's constraints: 60-90 (10:00-10:30), 150-180 (11:30-12:00), 270-300 (13:30-14:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 270, start >= 300))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Bradley's constraints: 30-60 (9:30-10:00), 90-150 (10:30-11:30), 270-300 (13:30-14:00), 330-360 (14:30-15:00), 390-480 (15:30-17:00)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 90, start >= 150))
    s.add(Or(start + duration <= 270, start >= 300))
    s.add(Or(start + duration <= 330, start >= 360))
    s.add(Or(start + duration <= 390, start >= 480))
    
    # Steven's constraints: 0-180 (9:00-12:00), 240-270 (13:00-13:30), 330-480 (14:30-17:00)
    s.add(Or(
        And(start >= 180, start + duration <= 240),  # 12:00-13:00
        And(start >= 270, start + duration <= 330)   # 13:30-14:30 (but blocked by Bradley)
    ))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Jerry's constraints: 150-180 (11:30-12:00), 420-450 (16:00-16:30)
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 420, start >= 450))
    
    # Benjamin: No constraints
    
    # Andrew's constraints: 30-90 (9:30-10:30), 150-210 (11:30-12:30), 240-270 (13:00-13:30), 300-390 (14:00-15:30)
    s.add(Or(start + duration <= 30, start >= 90))
    s.add(Or(start + duration <= 150, start >= 210))
    s.add(Or(start + duration <= 240, start >= 270))
    s.add(Or(start + duration <= 300, start >= 390))
    
    # Anna's constraints: 0-150 (9:00-11:30), 180-210 (12:00-12:30), 240-480 (13:00-17:00)
    s.add(start >= 150)  # Must start after 11:30
    s.add(Or(start + duration <= 180, start >= 210))
    s.add(start + duration <= 240)  # Must end by 13:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
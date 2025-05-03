from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 60  # One-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Olivia's constraints: 210-270 (12:30-13:30), 330-360 (14:30-15:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 210, start >= 270))
    s.add(Or(start + duration <= 330, start >= 360))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Anna has no constraints
    
    # Virginia's constraints: 0-60 (9:00-10:00), 150-420 (11:30-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 0, start >= 60))
    s.add(Or(start + duration <= 150, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Paul's constraints: 0-30 (9:00-9:30), 120-150 (11:00-11:30), 240-300 (13:00-14:00), 330-420 (14:30-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 120, start >= 150))
    s.add(Or(start + duration <= 240, start >= 300))
    s.add(Or(start + duration <= 330, start >= 420))
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
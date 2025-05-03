from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Ruth's constraints: 30-60 (9:30-10:00), 120-150 (11:00-11:30), 180-210 (12:00-12:30),
    # 240-270 (13:00-13:30), 330-360 (14:30-15:00), 420-450 (16:00-16:30)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 120, start >= 150))
    s.add(Or(start + duration <= 180, start >= 210))
    s.add(Or(start + duration <= 240, start >= 270))
    s.add(Or(start + duration <= 330, start >= 360))
    s.add(Or(start + duration <= 420, start >= 450))
    
    # Angela's constraints: 0-30 (9:00-9:30), 210-240 (12:30-13:00), 270-360 (13:30-15:00), 420-450 (16:00-16:30)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 210, start >= 240))
    s.add(Or(start + duration <= 270, start >= 360))
    s.add(Or(start + duration <= 420, start >= 450))
    
    # Lisa's constraints: 90-120 (10:30-11:00), 150-300 (11:30-14:00), 330-390 (14:30-15:30), 420-480 (16:00-17:00)
    s.add(Or(start + duration <= 90, start >= 120))
    s.add(Or(start + duration <= 150, start >= 300))
    s.add(Or(start + duration <= 330, start >= 390))
    s.add(Or(start + duration <= 420, start >= 480))
    
    # Cheryl's constraints: 0-90 (9:00-10:30), 120-150 (11:00-11:30), 210-300 (12:30-14:00), 420-450 (16:00-16:30)
    s.add(Or(start + duration <= 0, start >= 90))
    s.add(Or(start + duration <= 120, start >= 150))
    s.add(Or(start + duration <= 210, start >= 300))
    s.add(Or(start + duration <= 420, start >= 450))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
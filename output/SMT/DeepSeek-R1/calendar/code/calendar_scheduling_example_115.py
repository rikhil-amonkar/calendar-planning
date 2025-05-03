from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Jose: No constraints (free all day)
    
    # Catherine's constraints: 180-210 (12:00-12:30), 360-390 (15:00-15:30), prefers after 14:00 (300)
    s.add(Or(start + duration <= 180, start >= 210))  # Avoid 12:00-12:30
    s.add(Or(start + duration <= 360, start >= 390))  # Avoid 15:00-15:30
    s.add(start >= 300)  # Must start after 14:00
    
    # Rachel's constraints: 0-30 (9:00-9:30), 60-120 (10:00-11:00), 150-180 (11:30-12:00),
    # 210-240 (12:30-13:00), 300-420 (14:00-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 60, start >= 120))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 210, start >= 240))
    s.add(Or(start + duration <= 300, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Lori's constraints: 0-180 (9:00-12:00), 240-270 (13:00-13:30), 330-390 (14:30-15:30), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 0, start >= 180))   # Avoid 9:00-12:00
    s.add(Or(start + duration <= 240, start >= 270)) # Avoid 13:00-13:30
    s.add(Or(start + duration <= 330, start >= 390)) # Avoid 14:30-15:30
    s.add(Or(start + duration <= 450, start >= 480)) # Avoid 16:30-17:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
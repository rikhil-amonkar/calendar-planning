from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Lisa's constraints: 330+ (14:30+), blocked 360-420 (15:00-16:00)
    s.add(start >= 330)  # Can't meet before 14:30
    s.add(Or(start + duration <= 360, start >= 420))  # Avoid 15:00-16:00
    
    # Dorothy's constraints: 330-390 (14:30-15:30)
    s.add(Or(start + duration <= 330, start >= 390))  # Avoid 14:30-15:30
    
    # Anthony's constraints: 360-450 (15:00-16:30)
    s.add(Or(start + duration <= 360, start >= 450))  # Avoid 15:00-16:30
    
    # Ryan's constraints: Available only 450-480 (16:30-17:00)
    s.add(start >= 450)
    s.add(start + duration <= 480)
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
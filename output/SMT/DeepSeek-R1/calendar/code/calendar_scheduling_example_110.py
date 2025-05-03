from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Grace's preference: Avoid meetings after 15:00 (ends by 15:00 = 360 minutes)
    s.add(start + duration <= 360)
    
    # Helen's constraints: 0-180 (9:00-12:00), 210-300 (12:30-14:00), 330-360 (14:30-15:00)
    s.add(Or(start + duration <= 0, start >= 180))   # Avoid 9:00-12:00
    s.add(Or(start + duration <= 210, start >= 300)) # Avoid 12:30-14:00
    s.add(Or(start + duration <= 330, start >= 360)) # Avoid 14:30-15:00
    
    # Ashley's constraints: 0-30 (9:00-9:30), 60-90 (10:00-10:30), 120-300 (11:00-14:00)
    s.add(Or(start + duration <= 0, start >= 30))    # Avoid 9:00-9:30
    s.add(Or(start + duration <= 60, start >= 90))   # Avoid 10:00-10:30
    s.add(Or(start + duration <= 120, start >= 300)) # Avoid 11:00-14:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
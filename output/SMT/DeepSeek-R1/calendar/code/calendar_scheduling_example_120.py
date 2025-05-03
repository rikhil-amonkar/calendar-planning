from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Debra's constraints: 0-60 (9:00-10:00), 180-210 (12:00-12:30), 240-330 (13:00-14:30)
    s.add(Or(start + duration <= 0, start >= 60))
    s.add(Or(start + duration <= 180, start >= 210))
    s.add(Or(start + duration <= 240, start >= 330))
    
    # Christopher's constraints: 30-60 (9:30-10:00), 180-240 (12:00-13:00), 270-300 (13:30-14:00), 
    # 330-360 (14:30-15:00), 450-480 (16:30-17:00) + end by 240 (13:00)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 180, start >= 240))
    s.add(start + duration <= 240)  # Preference to end by 13:00
    
    # Evelyn's constraints: 30-90 (9:30-10:30), 150-180 (11:30-12:00), 210-330 (12:30-14:30), 390-420 (15:30-16:00)
    s.add(Or(start + duration <= 30, start >= 90))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 210, start >= 330))
    s.add(Or(start + duration <= 390, start >= 420))
    
    # Wayne's constraints: 0-30 (9:00-9:30), 60-90 (10:00-10:30), 120-210 (11:00-12:30), 
    # 240-270 (13:00-13:30), 300-420 (14:00-16:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 120, start >= 210))
    s.add(Or(start + duration <= 240, start >= 270))
    s.add(Or(start + duration <= 300, start >= 420))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
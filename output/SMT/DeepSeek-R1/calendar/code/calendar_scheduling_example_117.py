from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Brian's constraints: 0-30 (9:00-9:30), 180-240 (12:00-13:00), 300-330 (14:00-14:30)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 180, start >= 240))
    s.add(Or(start + duration <= 300, start >= 330))
    
    # Ronald's constraints: 60-90 (10:00-10:30), 150-180 (11:30-12:00), 300-330 (14:00-14:30), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 300, start >= 330))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Denise's constraints: 30-60 (9:30-10:00), 120-210 (11:00-12:30), 240-270 (13:00-13:30), 300-360 (14:00-15:00), 390-480 (15:30-17:00)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 120, start >= 210))
    s.add(Or(start + duration <= 240, start >= 270))
    s.add(Or(start + duration <= 300, start >= 360))
    s.add(Or(start + duration <= 390, start >= 480))
    
    # Jesse's constraints: 0-30 (9:00-9:30), 90-120 (10:30-11:00), 150-180 (11:30-12:00), 210-270 (12:30-13:30), 300-360 (14:00-15:00), 390-420 (15:30-16:00) + preference to end by 360 (15:00)
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 90, start >= 120))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 210, start >= 270))
    s.add(Or(start + duration <= 300, start >= 360))
    s.add(Or(start + duration <= 390, start >= 420))
    s.add(start + duration <= 360)  # End by 15:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
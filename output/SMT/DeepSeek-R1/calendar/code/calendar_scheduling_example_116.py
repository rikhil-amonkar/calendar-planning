from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Adam's constraints: 300-360 (14:00-15:00)
    s.add(Or(start + duration <= 300, start >= 360))
    
    # John's constraints: 240-270 (13:00-13:30), 300-330 (14:00-14:30), 390-420 (15:30-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 240, start >= 270))
    s.add(Or(start + duration <= 300, start >= 330))
    s.add(Or(start + duration <= 390, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Stephanie's constraints: 30-60 (9:30-10:00), 90-120 (10:30-11:00), 150-420 (11:30-16:00), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 90, start >= 120))
    s.add(Or(start + duration <= 150, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Anna's constraints: 30-60 (9:30-10:00), 180-210 (12:00-12:30), 240-390 (13:00-15:30), 450-480 (16:30-17:00) + prefer after 270 (14:30)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 180, start >= 210))
    s.add(Or(start + duration <= 240, start >= 390))
    s.add(Or(start + duration <= 450, start >= 480))
    s.add(start >= 270)  # Preference for after 14:30
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
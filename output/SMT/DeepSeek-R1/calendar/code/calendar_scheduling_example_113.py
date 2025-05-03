from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Bradley's constraints: 30-60 (9:30-10:00), 150-180 (12:30-13:00), 210-240 (13:30-14:00), 270-300 (15:30-16:00)
    s.add(Or(start + duration <= 30, start >= 60))   # Avoid 9:30-10:00
    s.add(Or(start + duration <= 150, start >= 180)) # Avoid 12:30-13:00
    s.add(Or(start + duration <= 210, start >= 240)) # Avoid 13:30-14:00
    s.add(Or(start + duration <= 270, start >= 300)) # Avoid 15:30-16:00
    
    # Teresa's constraints: 90-120 (10:30-11:00), 180-210 (12:00-12:30), 240-270 (13:00-13:30), 330-360 (14:30-15:00)
    s.add(Or(start + duration <= 90, start >= 120))   # Avoid 10:30-11:00
    s.add(Or(start + duration <= 180, start >= 210)) # Avoid 12:00-12:30
    s.add(Or(start + duration <= 240, start >= 270)) # Avoid 13:00-13:30
    s.add(Or(start + duration <= 330, start >= 360)) # Avoid 14:30-15:00
    
    # Elizabeth's constraints: 0-30 (9:00-9:30), 90-150 (10:30-11:30), 240-270 (13:00-13:30), 330-360 (14:30-15:00), 390-480 (15:30-17:00)
    s.add(Or(start + duration <= 0, start >= 30))    # Avoid 9:00-9:30
    s.add(Or(start + duration <= 90, start >= 150))  # Avoid 10:30-11:30
    s.add(Or(start + duration <= 240, start >= 270)) # Avoid 13:00-13:30
    s.add(Or(start + duration <= 330, start >= 360)) # Avoid 14:30-15:00
    s.add(start + duration <= 390)                   # Avoid 15:30-17:00
    
    # Christian's constraints: 0-30 (9:00-9:30), 90-480 (10:30-17:00)
    s.add(start >= 30)                               # Must start after 9:30
    s.add(start + duration <= 90)                    # Must end by 10:30
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
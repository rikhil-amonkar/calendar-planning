from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Jean's constraints: 120-150 (11:00-11:30), 210-270 (12:30-13:30), 300-330 (14:00-14:30), 360-390 (15:00-15:30), 450-480 (16:30-17:00)
    s.add(Or(start + duration <= 120, start >= 150))  # Avoid 11:00-11:30
    s.add(Or(start + duration <= 210, start >= 270))  # Avoid 12:30-13:30
    s.add(Or(start + duration <= 300, start >= 330))  # Avoid 14:00-14:30
    s.add(Or(start + duration <= 360, start >= 390))  # Avoid 15:00-15:30
    s.add(start + duration <= 450)                    # Avoid 16:30-17:00
    
    # Samuel's constraints: 0-180 (9:00-12:00), 210-420 (12:30-16:00), 450-480 (16:30-17:00)
    s.add(start >= 180)                               # Must start after 12:00
    s.add(Or(start + duration <= 210, start >= 420))  # Avoid 12:30-16:00
    s.add(start + duration <= 450)                    # Avoid 16:30-17:00
    
    # Henry's constraints: 0-90 (9:00-10:30), 300-330 (14:00-14:30), 360-480 (15:00-17:00)
    s.add(start >= 90)                                # Must start after 10:30
    s.add(Or(start + duration <= 300, start >= 330))  # Avoid 14:00-14:30
    s.add(start + duration <= 360)                    # Avoid 15:00-17:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
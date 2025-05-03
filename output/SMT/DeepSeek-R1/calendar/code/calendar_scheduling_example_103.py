from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # End by 17:00 (480 minutes)
    
    # Diane's constraints: 9:30-10:00 (30-60), 14:30-15:00 (330-360)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 330, start >= 360))
    
    # Jack's constraints: 13:30-14:00 (270-300), 14:30-15:00 (330-360)
    s.add(Or(start + duration <= 270, start >= 300))
    s.add(Or(start + duration <= 330, start >= 360))
    
    # Eugene's constraints: 9:00-10:00 (0-60), 10:30-11:30 (90-150), 12:00-14:30 (180-330), 15:00-16:30 (360-450)
    s.add(Or(start + duration <= 0, start >= 60))
    s.add(Or(start + duration <= 90, start >= 150))
    s.add(Or(start + duration <= 180, start >= 330))
    s.add(Or(start + duration <= 360, start >= 450))
    
    # Patricia's constraints: 9:30-10:30 (30-90), 11:00-12:00 (120-180), 12:30-14:00 (210-300), 15:00-16:30 (360-450)
    s.add(Or(start + duration <= 30, start >= 90))
    s.add(Or(start + duration <= 120, start >= 180))
    s.add(Or(start + duration <= 210, start >= 300))
    s.add(Or(start + duration <= 360, start >= 450))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
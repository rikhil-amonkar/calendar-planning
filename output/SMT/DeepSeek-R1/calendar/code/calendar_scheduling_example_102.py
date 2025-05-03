from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 60  # 1 hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00 (480 minutes)
    
    # Dylan's constraints: busy 14:00-15:00 (300-360 minutes)
    s.add(Or(start + duration <= 300, start >= 360))
    
    # Kathryn's constraints: busy 9:00-9:30 (0-30) and 10:00-10:30 (60-90)
    s.add(start >= 90)  # Must start after 10:30
    
    # Hannah's constraints: busy 9:00-10:30 (0-90), 12:30-15:30 (210-390), 16:00-16:30 (420-450)
    s.add(Or(start + duration <= 210, start >= 390))
    s.add(Or(start + duration <= 420, start >= 450))
    
    # Anna's constraints: busy 9:00-11:00 (0-120), 12:00-14:00 (180-300), 14:30-15:00 (330-360), 16:00-16:30 (420-450)
    s.add(start >= 120)  # Must start after 11:00
    s.add(Or(start + duration <= 180, start >= 300))
    s.add(Or(start + duration <= 330, start >= 360))
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
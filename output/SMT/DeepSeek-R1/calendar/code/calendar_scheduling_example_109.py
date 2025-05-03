from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00 (handled later by Theresa's constraints)
    
    # Marie's constraints: 11:00-11:30 (120-150), 15:00-16:30 (360-450)
    s.add(Or(start + duration <= 120, start >= 150))
    
    # Elijah's constraints: 10:00-13:00 (60-240), 14:30-15:00 (330-360), 16:00-16:30 (420-450)
    s.add(Or(start + duration <= 60, start >= 240))
    
    # Theresa's constraints: ends by 12:00 (180) and avoids 9:30-10:30 (30-90)
    s.add(start + duration <= 180)
    s.add(Or(start + duration <= 30, start >= 90))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
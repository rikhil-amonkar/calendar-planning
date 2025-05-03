from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Karen's constraints: busy 9:00-10:30 (0-90), 16:30-17:00 (450-480)
    s.add(start >= 90)  # Start after 10:30
    s.add(start + duration <= 450)  # End by 16:30
    
    # Brandon's constraints: busy 9:30-10:00 (30-60), 10:30-11:00 (90-120), 11:30-12:30 (150-180), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    s.add(Or(start + duration <= 30, start >= 60))
    s.add(Or(start + duration <= 90, start >= 120))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 390, start >= 420))
    s.add(start + duration <= 450)  # End before 16:30
    
    # Donald's constraints: busy 9:00-10:30 (0-90), 11:00-14:00 (120-300), 14:30-17:00 (330-480)
    s.add(start >= 90)  # Start after 10:30
    s.add(Or(start + duration <= 120, start >= 300))  # Avoid 11:00-14:00 block
    s.add(start + duration <= 330)  # End before 14:30
    
    # Kelly's constraints: busy 9:00-9:30 (0-30), 10:30-11:00 (90-120), 11:30-12:00 (150-180), 13:30-14:00 (270-300), 14:30-15:30 (330-390), 16:00-17:00 (420-480)
    s.add(start >= 30)  # Start after 9:30
    s.add(Or(start + duration <= 90, start >= 120))  # Avoid 10:30-11:00
    s.add(Or(start + duration <= 150, start >= 180))  # Avoid 11:30-12:00
    s.add(Or(start + duration <= 270, start >= 300))  # Avoid 13:30-14:00
    s.add(Or(start + duration <= 330, start >= 390))  # Avoid 14:30-15:30
    s.add(start + duration <= 420)  # End before 16:00
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
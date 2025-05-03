from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    duration = 30  # Half-hour meeting
    
    # Convert times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + duration <= 480)  # Must end by 17:00
    
    # Jason's constraints: 0-60, 90-120, 150-180, 210-240, 300-330
    s.add(Or(start + duration <= 0, start >= 60))
    s.add(Or(start + duration <= 90, start >= 120))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 210, start >= 240))
    s.add(Or(start + duration <= 300, start >= 330))
    
    # William's constraints: 0-30, 150-180, 300-330, 450-480
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 150, start >= 180))
    s.add(Or(start + duration <= 300, start >= 330))
    s.add(Or(start + duration <= 450, start >= 480))
    
    # Frances's constraints: 0-30, 60-90, 120-210, 270-420
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 120, start >= 210))
    s.add(Or(start + duration <= 270, start >= 420))
    
    # Rachel's constraints: 0-30, 60-90, 120-300, 330-420, 450-480
    s.add(Or(start + duration <= 0, start >= 30))
    s.add(Or(start + duration <= 60, start >= 90))
    s.add(Or(start + duration <= 120, start >= 300))
    s.add(Or(start + duration <= 330, start >= 420))
    s.add(Or(start + duration <= 450, start >= 480))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
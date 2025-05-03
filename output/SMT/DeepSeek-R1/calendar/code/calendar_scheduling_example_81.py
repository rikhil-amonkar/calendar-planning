from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (9:00 = 0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Jeremy's constraints (14:30-15:30 → 330-390)
    s.add(Or(start + meeting_duration <= 330, start >= 390))
    
    # Lawrence's constraints (15:30-16:00 → 390-420, 16:30-17:00 → 450-480)
    s.add(Or(start + meeting_duration <= 390, start >= 420))  # 390-420
    s.add(Or(start + meeting_duration <= 450, start >= 480))  # 450-480
    
    # Helen's constraints
    # 9:30-10:00 (30-60)
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 10:30-11:00 (90-120)
    s.add(Or(start + meeting_duration <= 90, start >= 120))
    # 11:30-12:00 (150-180)
    s.add(Or(start + meeting_duration <= 150, start >= 180))
    # 13:00-14:00 (240-300)
    s.add(Or(start + meeting_duration <= 240, start >= 300))
    # 15:00-15:30 (360-390)
    s.add(Or(start + meeting_duration <= 360, start >= 390))
    # 16:00-17:00 (420-480)
    s.add(Or(start + meeting_duration <= 420, start >= 480))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Adam's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(Or(start + meeting_duration <= 30, start >= 60))
    # 10:30-11:00 → 90-120 minutes
    s.add(Or(start + meeting_duration <= 90, start >= 120))
    # 11:30-12:00 → 150-180 minutes
    s.add(Or(start + meeting_duration <= 150, start >= 180))
    # 16:30-17:00 → 450-480 minutes
    s.add(Or(start + meeting_duration <= 450, start >= 480))
    
    # Willie's constraints
    # 9:00-9:30 → 0-30 minutes
    s.add(start >= 30)
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    
    # Gloria's constraints
    # 9:30-12:30 → 30-210 minutes
    s.add(start >= 210)
    # 13:00-13:30 → 240-270 minutes
    s.add(Or(start + meeting_duration <= 240, start >= 270))
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    
    # Gloria's preference to avoid meetings after 15:30 (390 minutes)
    s.add(start + meeting_duration <= 390)
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
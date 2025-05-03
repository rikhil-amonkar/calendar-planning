from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Jacqueline's constraints
    # 9:30-10:00 → 30-60 minutes
    s.add(start >= 60)  # Must start after 10:00
    # 16:30-17:00 → 450-480 minutes
    s.add(start + meeting_duration <= 450)  # Must end by 16:30
    
    # Henry has no constraints (free all day)
    
    # William's constraints
    # 9:30-10:30 → 30-90 minutes
    s.add(start >= 90)  # Must start after 10:30
    # 12:30-15:00 → 210-360 minutes
    s.add(start + meeting_duration <= 210)  # Must end by 12:30
    # 15:30-17:00 → 390-480 minutes (covered by end time <=480)
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
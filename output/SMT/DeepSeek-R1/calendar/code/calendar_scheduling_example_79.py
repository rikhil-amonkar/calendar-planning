from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 60  # 1 hour
    
    # Convert all times to minutes since 9:00 (9:00 = 0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Amy's constraints (busy 11:00-11:30 (120-150), 12:00-12:30 (180-210))
    s.add(Or(start + meeting_duration <= 120, start >= 150))  # Avoid 120-150
    s.add(Or(start + meeting_duration <= 180, start >= 210))  # Avoid 180-210
    
    # John's constraints
    # Busy: 10:00-10:30 (60-90), 11:30-12:00 (150-180), 12:30-16:00 (210-420), 16:30-17:00 (450-480)
    s.add(Or(start + meeting_duration <= 60, start >= 90))     # Avoid 60-90
    s.add(Or(start + meeting_duration <= 150, start >= 180))   # Avoid 150-180
    s.add(Or(start + meeting_duration <= 210, start >= 420))   # Avoid 210-420
    s.add(Or(start + meeting_duration <= 450, start >= 480))   # Avoid 450-480
    
    # Emma has no constraints
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
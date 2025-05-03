from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # 17:00 = 480 minutes
    
    # Donald's constraints
    # Must end by 12:00 (180 minutes) and avoid specific blocks
    s.add(start + meeting_duration <= 180)  # End by 12:00
    # Avoid 10:00-10:30 (60-90), 11:00-11:30 (120-150)
    s.add(Or(start + meeting_duration <= 60, start >= 90))  # 60-90 block
    s.add(Or(start + meeting_duration <= 120, start >= 150))  # 120-150 block
    
    # Joyce's constraints
    # Avoid 11:00-13:00 (120-240)
    s.add(Or(start + meeting_duration <= 120, start >= 240))
    
    # Abigail's constraints
    # Avoid 9:30-10:00 (30-60), 11:30-12:00 (150-180)
    s.add(Or(start + meeting_duration <= 30, start >= 60))  # 30-60 block
    # 150-180 block automatically handled by end time constraint
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Austin's constraints
    # 10:30-11:00 → 90-120 minutes
    s.add(Or(start + meeting_duration <= 90, start >= 120))
    # 13:30-14:00 → 270-300 minutes
    s.add(Or(start + meeting_duration <= 270, start >= 300))
    
    # Danielle's constraints
    # 9:00-10:00 → 0-60 minutes
    s.add(start >= 60)
    # 11:00-12:00 → 120-180 minutes
    s.add(Or(start + meeting_duration <= 120, start >= 180))
    # 13:00-13:30 → 240-270 minutes
    s.add(Or(start + meeting_duration <= 240, start >= 270))
    # 15:30-16:00 → 390-420 minutes
    s.add(Or(start + meeting_duration <= 390, start >= 420))
    
    # Charles's constraints
    # Free slots: 11:30-12:00 (150-180) and 12:30-13:00 (210-240)
    s.add(Or(
        And(start >= 150, start + meeting_duration <= 180),
        And(start >= 210, start + meeting_duration <= 240)
    ))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
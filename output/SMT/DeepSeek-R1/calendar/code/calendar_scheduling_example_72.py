from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    total_minutes = 17 * 60 - 9 * 60  # 480 minutes (9:00 to 17:00)
    meeting_duration = 60
    
    # Start must be within 0-420 minutes to fit 1h meeting
    s.add(start >= 0)
    s.add(start + meeting_duration <= total_minutes)
    
    # Amy's blocked times: 9:30-11:30 (30-150), 13:00-13:30 (240-270), 16:30-17:00 (450-480)
    s.add(start >= 150)                          # After 11:30
    s.add(Or(start >= 270, start + 60 <= 240))   # Avoid 13:00-13:30
    s.add(start + 60 <= 450)                      # End before 16:30
    
    # Christopher's blocked times: 9:00-10:00 (0-60), 12:00-13:30 (180-270), 
    # 14:30-15:00 (330-360), 15:30-16:30 (390-450)
    s.add(start >= 60)                            # Start after 10:00
    s.add(Or(start >= 270, start + 60 <= 180))    # Avoid 12:00-13:30
    s.add(Or(start >= 360, start + 60 <= 330))    # Avoid 14:30-15:00
    s.add(start + 60 <= 390)                      # End before 15:30
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
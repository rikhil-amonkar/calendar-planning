from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    total_minutes = 17 * 60 - 9 * 60  # 480 minutes (9:00 to 17:00)
    meeting_duration = 60
    
    # Base constraints for time window and duration
    s.add(start >= 0)
    s.add(start + meeting_duration <= total_minutes)
    
    # Eric's constraints
    # Busy 10:00-12:00 (60-180 minutes), meeting must end before 15:30 (390 minutes)
    s.add(Or(start + meeting_duration <= 60, start >= 180))  # Avoid 10:00-12:00
    s.add(start + meeting_duration <= 390)  # End by 15:30
    
    # Albert's constraints
    # Busy 12:00-12:30 (180-210), 15:30-16:00 (390-420)
    s.add(Or(start + meeting_duration <= 180, start >= 210))  # Avoid 12:00-12:30
    s.add(Or(start + meeting_duration <= 390, start >= 420))  # Avoid 15:30-16:00
    
    # Katherine's constraints
    # Busy 10:00-11:00 (60-120), 11:30-14:00 (150-300), 15:00-15:30 (360-390)
    s.add(Or(start + meeting_duration <= 60, start >= 120))  # Avoid 10:00-11:00
    s.add(Or(start + meeting_duration <= 150, start >= 300))  # Avoid 11:30-14:00
    s.add(Or(start + meeting_duration <= 360, start >= 390))  # Avoid 15:00-15:30
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
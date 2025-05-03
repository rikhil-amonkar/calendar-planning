from z3 import *

def schedule_meeting():
    s = Solver()
    start = Int('start')
    meeting_duration = 30  # Half-hour meeting
    
    # Convert all times to minutes since 9:00 (9:00 = 0 minutes)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # End by 17:00 (480 minutes)
    
    # Michelle's constraints
    s.add(Or(start + meeting_duration <= 30, start >= 60))   # 9:30-10:00 (30-60)
    s.add(Or(start + meeting_duration <= 210, start >= 240)) # 12:30-13:00 (210-240)
    
    # Billy's constraints
    s.add(Or(start + meeting_duration <= 90, start >= 120))  # 10:30-11:00 (90-120)
    s.add(Or(start + meeting_duration <= 150, start >= 180)) # 11:30-12:00 (150-180)
    s.add(Or(start + meeting_duration <= 330, start >= 360)) # 14:30-15:00 (330-360)
    s.add(Or(start + meeting_duration <= 420, start >= 450)) # 16:00-16:30 (420-450)
    
    # Alexis's constraints + preference
    s.add(Or(start + meeting_duration <= 30, start >= 90))   # 9:30-10:30 (30-90)
    s.add(Or(start + meeting_duration <= 120, start >= 180)) # 11:00-12:00 (120-180)
    s.add(Or(start + meeting_duration <= 210, start >= 240)) # 12:30-13:00 (210-240)
    s.add(Or(start + meeting_duration <= 270, start >= 330)) # 13:30-14:30 (270-330)
    s.add(start <= 330)  # Preference: end by 15:00 (360 minutes)
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
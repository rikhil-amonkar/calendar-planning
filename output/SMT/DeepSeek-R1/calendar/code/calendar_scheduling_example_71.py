from z3 import *

def schedule_meeting():
    # Initialize solver
    s = Solver()
    
    # Meeting start time in minutes after 9:00
    start = Int('start')
    
    # Meeting must be within 9:00-17:00 and duration 30 minutes
    s.add(start >= 0)
    s.add(start + 30 <= 480)  # 480 minutes = 17:00
    
    # John's constraints (blocked times and preference)
    # Blocked: 12:30-13:00 (210-240 minutes), 16:30-17:00 (450-480)
    s.add(Or(start >= 240, start + 30 <= 210))
    s.add(start + 30 <= 450)
    # John's preference: before 12:00 (180 minutes)
    s.add(start < 180)
    
    # Ethan's constraints (blocked times)
    # Blocked: 9:00-10:00 (0-60), 11:30-14:00 (150-300), 14:30-17:00 (330-480)
    s.add(start >= 60)
    s.add(Or(start >= 300, start + 30 <= 150))
    s.add(Or(start >= 480, start + 30 <= 330))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        hours = 9 + start_min // 60
        minutes = start_min % 60
        print(f"Meeting starts at {hours:02d}:{minutes:02d}")
    else:
        print("No valid time found.")

schedule_meeting()
from z3 import *

def find_meeting_time():
    s = Solver()
    start = Int('start')
    
    # Meeting must be within 9:00 (0 min) to 17:00 (480 min)
    s.add(start >= 0)
    s.add(start + 60 <= 480)  # Duration is 60 minutes
    
    # James's busy intervals in minutes since 9:00
    james_busy = [(150, 180), (330, 360)]
    for begin, end in james_busy:
        s.add(Or(start + 60 <= begin, start >= end))
    
    # John's busy intervals
    john_busy = [(30, 120), (150, 180), (210, 270), (330, 450)]
    for begin, end in john_busy:
        s.add(Or(start + 60 <= begin, start >= end))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        end_min = start_min + 60
        
        # Convert minutes to time strings
        start_h = 9 + start_min // 60
        start_m = start_min % 60
        end_h = 9 + end_min // 60
        end_m = end_min % 60
        
        return f"Monday {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}"
    else:
        return "No valid time found"

print(find_meeting_time())
from z3 import *
import json

# Initialize variables for meeting start and end times (in minutes from 9:00 AM)
jason_start = Int('jason_start')
jason_end = Int('jason_end')
jessica_start = Int('jessica_start')
jessica_end = Int('jessica_end')
sandra_start = Int('sandra_start')
sandra_end = Int('sandra_end')

s = Solver()

# Jason's constraints (Fisherman's Wharf: 16:00 to 16:45, min 30 minutes)
s.add(jason_start >= 420)   # 16:00 is 420 minutes after 9:00 AM
s.add(jason_end <= 465)     # 16:45 is 465 minutes after 9:00 AM
s.add(jason_end - jason_start >= 30)

# Jessica's constraints (Embarcadero: 16:45 to 19:00, min 30 minutes)
s.add(jessica_start >= 465) # 16:45 is 465 minutes after 9:00 AM
s.add(jessica_end <= 600)   # 19:00 is 600 minutes after 9:00 AM
s.add(jessica_end - jessica_start >= 30)

# Sandra's constraints (Richmond District: 18:30 to 21:45, min 120 minutes)
s.add(sandra_start >= 570)   # 18:30 is 570 minutes after 9:00 AM
s.add(sandra_end <= 765)     # 21:45 is 765 minutes after 9:00 AM
s.add(sandra_end - sandra_start >= 120)

# Travel constraints
s.add(jessica_start >= jason_end + 8)   # Travel from Fisherman's Wharf to Embarcadero (8 minutes)
s.add(sandra_start >= jessica_end + 21) # Travel from Embarcadero to Richmond District (21 minutes)

# Check for a feasible schedule
if s.check() == sat:
    m = s.model()
    js_start = m.eval(jason_start).as_long()
    js_end = m.eval(jason_end).as_long()
    jes_start = m.eval(jessica_start).as_long()
    jes_end = m.eval(jessica_end).as_long()
    sa_start = m.eval(sandra_start).as_long()
    sa_end = m.eval(sandra_end).as_long()
    
    # Convert minutes from 9:00 AM to 24-hour time
    def format_time(minutes):
        total_minutes = 540 + minutes  # 9:00 AM is 540 minutes from midnight
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": format_time(js_start), "end_time": format_time(js_end)},
        {"action": "meet", "person": "Jessica", "start_time": format_time(jes_start), "end_time": format_time(jes_end)},
        {"action": "meet", "person": "Sandra", "start_time": format_time(sa_start), "end_time": format_time(sa_end)}
    ]
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("SOLUTION: No solution found")
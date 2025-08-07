from z3 import *
import json

def min_to_time(minutes):
    total_minutes = int(minutes)
    hours = total_minutes // 60
    mins = total_minutes % 60
    total_hours = 9 + hours
    return f"{total_hours:02d}:{mins:02d}"

s_helen = Int('s_helen')
s_kimberly = Int('s_kimberly')
s_patricia = Int('s_patricia')

s = Solver()

s.add(s_helen >= 8)
s.add(s_helen + 120 <= 465)

s.add(s_kimberly >= 450)
s.add(s_kimberly + 45 <= 720)

s.add(s_patricia >= 540)
s.add(s_patricia + 120 <= 735)

s.add(s_kimberly >= s_helen + 125)
s.add(s_patricia >= s_kimberly + 71)

if s.check() == sat:
    m = s.model()
    helen_start = m[s_helen].as_long()
    kimberly_start = m[s_kimberly].as_long()
    patricia_start = m[s_patricia].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Helen", "start_time": min_to_time(helen_start), "end_time": min_to_time(helen_start + 120)},
        {"action": "meet", "person": "Kimberly", "start_time": min_to_time(kimberly_start), "end_time": min_to_time(kimberly_start + 45)},
        {"action": "meet", "person": "Patricia", "start_time": min_to_time(patricia_start), "end_time": min_to_time(patricia_start + 120)}
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')
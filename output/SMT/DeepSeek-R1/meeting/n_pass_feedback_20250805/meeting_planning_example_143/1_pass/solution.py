import json
from z3 import *

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_both():
    mark_start = Int('mark_start')
    s = Solver()
    
    mark_available_start = 13 * 60  # 1:00 PM
    mark_available_end = 17 * 60 + 45  # 5:45 PM
    mark_duration = 120
    karen_start_time = 18 * 60 + 45  # 6:45 PM
    travel_time = 11  # Embarcadero to Pacific Heights
    
    s.add(mark_start >= mark_available_start)
    s.add(mark_start + mark_duration <= mark_available_end)
    s.add(mark_start + mark_duration + travel_time <= karen_start_time)
    
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(mark_start)
    
    if opt.check() == sat:
        m = opt.model()
        mark_start_val = m[mark_start].as_long()
        mark_end_val = mark_start_val + mark_duration
        karen_end_val = karen_start_time + 90  # 90 minutes meeting
        
        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_start_val), "end_time": minutes_to_time(mark_end_val)},
            {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_start_time), "end_time": minutes_to_time(karen_end_val)}
        ]
        return itinerary
    else:
        return None

def schedule_mark_only():
    mark_start_val = 13 * 60  # 1:00 PM
    mark_end_val = mark_start_val + 120  # 120 minutes meeting
    return [
        {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_start_val), "end_time": minutes_to_time(mark_end_val)}
    ]

def schedule_karen_only():
    karen_start_val = 18 * 60 + 45  # 6:45 PM
    karen_end_val = karen_start_val + 90  # 90 minutes meeting
    return [
        {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_start_val), "end_time": minutes_to_time(karen_end_val)}
    ]

# Main logic
itinerary = schedule_both()
if itinerary is not None:
    result = {"itinerary": itinerary}
else:
    itinerary_mark = schedule_mark_only()
    itinerary_karen = schedule_karen_only()
    result = {"itinerary": itinerary_mark}  # Prefer Mark if both individual meetings are feasible

print(json.dumps(result))
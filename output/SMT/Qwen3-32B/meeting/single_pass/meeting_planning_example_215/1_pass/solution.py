import json
from z3 import *

def to_time_str(minutes):
    hours = 9 + (minutes // 60)
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

# Variables for start times of each meeting
jason_start = Int('jason_start')
jessica_start = Int('jessica_start')
sandra_start = Int('sandra_start')

# Jason's meeting constraints: available 4:00-4:45 PM (420-465 minutes)
# Must have at least 30 minutes
solver.add(jason_start >= 420)
solver.add(jason_start <= 435)  # 435 + 30 = 465

# Jessica's meeting: available 4:45-7:00 PM (465-600 minutes)
# At least 30 minutes
solver.add(jessica_start >= 465)
solver.add(jessica_start <= 570)  # 570 + 30 = 600

# Sandra's meeting: available 6:30-9:45 PM (570-765 minutes)
# At least 120 minutes
solver.add(sandra_start >= 570)
solver.add(sandra_start <= 645)  # 645 + 120 = 765

# Transition constraints
# After Jason's meeting, travel to Embarcadero (8 minutes)
solver.add(jason_start + 30 + 8 <= jessica_start)
# After Jessica's meeting, travel to Richmond District (21 minutes)
solver.add(jessica_start + 30 + 21 <= sandra_start)

if solver.check() == sat:
    model = solver.model()
    # Extract the values
    js_val = model[jason_start].as_long()
    jess_val = model[jessica_start].as_long()
    sandra_val = model[sandra_start].as_long()

    # Create the itinerary entries
    jason_meet = {
        "action": "meet", 
        "person": "Jason", 
        "start_time": to_time_str(js_val), 
        "end_time": to_time_str(js_val + 30)
    }
    jessica_meet = {
        "action": "meet", 
        "person": "Jessica", 
        "start_time": to_time_str(jess_val), 
        "end_time": to_time_str(jess_val + 30)
    }
    sandra_meet = {
        "action": "meet", 
        "person": "Sandra", 
        "start_time": to_time_str(sandra_val), 
        "end_time": to_time_str(sandra_val + 120)
    }

    itinerary = [jason_meet, jessica_meet, sandra_meet]

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    # No solution for this order, but according to our analysis, there is one.
    # Maybe another order?
    pass
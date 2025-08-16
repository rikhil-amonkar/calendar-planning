from z3 import *
import json

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

opt = Optimize()

T_depart = Int('T_depart')

# Constraints
opt.add(T_depart >= 9 * 60)  # Arrive at Russian Hill at 9:00 AM (540 min)
opt.add(T_depart + 7 + 60 <= 22 * 60)  # Meeting ends by 10:00 PM (1320 min)

# Objective: Minimize departure time to get earliest possible meeting
opt.minimize(T_depart)

if opt.check() == sat:
    model = opt.model()
    depart = model[T_depart].as_long()
    start = depart + 7
    end = start + 60
    
    itinerary = [{
        "action": "meet",
        "person": "Barbara",
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    }]
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
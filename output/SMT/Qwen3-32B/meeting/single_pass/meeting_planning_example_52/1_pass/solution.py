import json
from z3 import *

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

solver = Solver()

T_depart = Int('T_depart')
S_start = Int('S_start')

# Constraints
solver.add(T_depart >= 540)  # 9:00 AM in minutes
solver.add(S_start >= T_depart + 14)  # Arrival time at Richmond
solver.add(S_start >= 795)  # Barbara's earliest availability (1:15 PM)
solver.add(S_start + 45 <= 1095)  # Barbara's latest end time (6:15 PM)

if solver.check() == sat:
    model = solver.model()
    s_start_val = model.evaluate(S_start).as_long()
    end_val = s_start_val + 45
    start_time = minutes_to_time(s_start_val)
    end_time = minutes_to_time(end_val)
    itinerary = [{"action": "meet", "person": "Barbara", "start_time": start_time, "end_time": end_time}]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
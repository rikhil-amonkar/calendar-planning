import json
from z3 import *

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

solver = Solver()

start_m = Int('start_m')
start_a = Int('start_a')
start_r = Int('start_r')

# Constraints for Melissa (North Beach)
# Arrival at North Beach: 540 (start time) + 29 (Sunset to NB) = 569
solver.add(start_m >= 569)
solver.add(start_m <= 705)  # 705 + 105 = 810

# Constraints for Anthony (Chinatown)
solver.add(start_a >= 795)
solver.add(start_a <= 810)  # 810 + 60 = 870

# Constraints for Rebecca (Russian Hill)
solver.add(start_r == 1170)

# Transition from Melissa to Anthony: NB to Chinatown (6 min)
solver.add(start_a >= start_m + 105 + 6)

# Transition from Anthony to Rebecca: Chinatown to Russian Hill (7 min)
solver.add(start_r >= start_a + 60 + 7)

if solver.check() == sat:
    model = solver.model()
    start_m_val = model[start_m].as_long()
    start_a_val = model[start_a].as_long()
    start_r_val = model[start_r].as_long()

    end_m_val = start_m_val + 105
    end_a_val = start_a_val + 60
    end_r_val = start_r_val + 105

    itinerary = [
        {
            "action": "meet",
            "location": "North Beach",
            "person": "Melissa",
            "start_time": to_time_str(start_m_val),
            "end_time": to_time_str(end_m_val)
        },
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "Anthony",
            "start_time": to_time_str(start_a_val),
            "end_time": to_time_str(end_a_val)
        },
        {
            "action": "meet",
            "location": "Russian Hill",
            "person": "Rebecca",
            "start_time": to_time_str(start_r_val),
            "end_time": to_time_str(end_r_val)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))
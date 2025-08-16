import json
from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

barbara_start = Int('barbara_start')
barbara_end = Int('barbara_end')
kenneth_start = Int('kenneth_start')
kenneth_end = Int('kenneth_end')

# Constraints for Barbara's meeting
s.add(barbara_start >= 540 + 23)  # 9:00 AM + 23 min (FD to GGP)
s.add(barbara_end >= barbara_start + 45)
s.add(barbara_end <= 19 * 60)  # 7:00 PM

# Constraints for Kenneth's meeting
s.add(kenneth_start >= barbara_end + 23)  # 23 min travel from GGP to Chinatown
s.add(kenneth_start >= 12 * 60)  # 12:00 PM
s.add(kenneth_end >= kenneth_start + 90)
s.add(kenneth_end <= 15 * 60)  # 3:00 PM

if s.check() == sat:
    model = s.model()
    bs = model[barbara_start].as_long()
    be = model[barbara_end].as_long()
    ks = model[kenneth_start].as_long()
    ke = model[kenneth_end].as_long()
    
    barbara_start_str = minutes_to_time(bs)
    barbara_end_str = minutes_to_time(be)
    kenneth_start_str = minutes_to_time(ks)
    kenneth_end_str = minutes_to_time(ke)
    
    itinerary = [
        {"action": "meet", "person": "Barbara", "start_time": barbara_start_str, "end_time": barbara_end_str},
        {"action": "meet", "person": "Kenneth", "start_time": kenneth_start_str, "end_time": kenneth_end_str}
    ]
    solution = {"itinerary": itinerary}
    print(json.dumps(solution, indent=2))
else:
    # Fallback if no solution found (not expected in this case)
    solution = {"itinerary": []}
    print(json.dumps(solution))
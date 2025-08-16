from z3 import *
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Initialize solver
solver = Solver()

# Define variables
L = Int('L')  # Departure from Fisherman's Wharf (minutes since midnight)
S = Int('S')  # Arrival at Nob Hill (start of meeting)

# Constraints
solver.add(S == L + 11)          # Travel time from Fisherman's Wharf to Nob Hill
solver.add(L >= 9 * 60)          # Can't leave Fisherman's Wharf before 9:00AM
solver.add(S >= 14 * 60 + 15)    # Kenneth available from 2:15PM
solver.add(S <= 18 * 60 + 15)    # Must finish meeting by 7:45PM (90min meeting)

if solver.check() == sat:
    model = solver.model()
    start_minutes = model[S].as_long()
    end_minutes = start_minutes + 90
    
    itinerary = [{
        "action": "meet",
        "person": "Kenneth",
        "start_time": to_time_str(start_minutes),
        "end_time": to_time_str(end_minutes)
    }]
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
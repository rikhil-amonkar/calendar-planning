from z3 import *
import json

def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Z3 solver setup
solver = Solver()

# Variables for meeting start and end times (in minutes since midnight)
S = Int('S')
E = Int('E')

# Daniel's availability constraints
daniel_start = to_minutes("19:00")  # 1140 minutes
daniel_end = to_minutes("20:15")    # 1215 minutes

# Add constraints
solver.add(S >= daniel_start)          # Meeting must start after Daniel arrives
solver.add(E <= daniel_end)            # Meeting must end before Daniel leaves
solver.add(E - S >= 75)                # Minimum meeting duration

# Check for solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = model[E].as_long()
    
    # Verify travel time feasibility
    departure_russian_hill = start_time - 14  # 14 min travel to Richmond
    if departure_russian_hill >= to_minutes("09:00"):  # Can't leave before 9:00AM
        itinerary = [{
            "action": "meet",
            "person": "Daniel",
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        }]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))
else:
    print(json.dumps({"itinerary": []}))
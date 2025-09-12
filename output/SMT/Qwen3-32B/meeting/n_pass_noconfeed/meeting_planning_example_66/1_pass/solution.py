import z3
import json

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

solver = z3.Solver()

# Variables
D = z3.Int('D')  # Departure time from Nob Hill in minutes since midnight

# Constraints
# You arrive at Nob Hill at 9:00 AM (540 min)
# Robert is available from 11:15 AM (675) to 5:45 PM (1065)
# Travel time Nob Hill to Presidio: 17 min
# Minimum meeting duration: 120 min

solver.add(D >= 540)  # Can't depart Nob Hill before arrival there
solver.add(D + 17 >= 675)  # Must arrive at Presidio by Robert's start time
solver.add(D + 17 + 120 <= 1065)  # Meeting must end by Robert's end time

if solver.check() == z3.sat:
    model = solver.model()
    D_val = model[D].as_long()
    start_meet = D_val + 17
    end_meet = start_meet + 120
    itinerary = [
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": time_str(start_meet),
            "end_time": time_str(end_meet)
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
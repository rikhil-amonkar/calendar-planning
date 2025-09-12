from z3 import *
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define variables for start times of meetings
S_L = Int('S_L')  # Laura's meeting start time in minutes since midnight
S_A = Int('S_A')  # Anthony's meeting start time in minutes since midnight

# Solver instance
solver = Solver()

# Scenario 1: Laura first, then Anthony
scenario1_constraints = [
    S_L >= 540 + 7,  # Castro to Mission travel time
    S_L >= 735,       # Laura's earliest available time
    S_L + 75 <= 1065, # Laura's meeting duration
    S_A >= (S_L + 75 + 17),  # Mission to Financial District travel time
    S_A >= 750,       # Anthony's earliest available time
    S_A + 30 <= 885   # Anthony's meeting duration
]

# Scenario 2: Anthony first, then Laura
scenario2_constraints = [
    S_A >= 540 + 20,  # Castro to Financial District travel time
    S_A >= 750,       # Anthony's earliest available time
    S_A + 30 <= 885,  # Anthony's meeting duration
    S_L >= (S_A + 30 + 17),  # Financial District to Mission travel time
    S_L >= 735,       # Laura's earliest available time
    S_L + 75 <= 1065  # Laura's meeting duration
]

# Add constraints for either scenario
solver.add(Or(And(scenario1_constraints), And(scenario2_constraints)))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    sl_val = model[S_L].as_long()
    sa_val = model[S_A].as_long()
    
    # Determine itinerary order
    if sl_val < sa_val:
        itinerary = [
            {
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": to_time_str(sl_val),
                "end_time": to_time_str(sl_val + 75)
            },
            {
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": to_time_str(sa_val),
                "end_time": to_time_str(sa_val + 30)
            }
        ]
    else:
        itinerary = [
            {
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": to_time_str(sa_val),
                "end_time": to_time_str(sa_val + 30)
            },
            {
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": to_time_str(sl_val),
                "end_time": to_time_str(sl_val + 75)
            }
        ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid meeting schedule found"}))
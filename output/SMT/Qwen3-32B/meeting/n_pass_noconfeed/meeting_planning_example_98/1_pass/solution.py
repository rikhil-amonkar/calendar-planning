from z3 import *
import json

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# Define variables
T = Int('T')  # Departure time from Alamo Square (minutes since midnight)
S = Int('S')  # Meeting start time
E = Int('E')  # Meeting end time

solver = Solver()

# Constraints
solver.add(T >= time_to_minutes('9:00'))  # Arrive at Alamo Square at 9:00 AM
solver.add(S >= T + 12)  # Must arrive at Richmond before meeting starts
solver.add(S >= time_to_minutes('20:45'))  # Timothy's earliest availability
solver.add(E == S + 45)  # Minimum meeting duration
solver.add(E <= time_to_minutes('21:30'))  # Timothy's latest availability

if solver.check() == sat:
    model = solver.model()
    T_val = model[T].as_long()
    S_val = model[S].as_long()
    E_val = model[E].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Timothy",
            "start_time": minutes_to_time(S_val),
            "end_time": minutes_to_time(E_val)
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
from z3 import *
import json

def time_to_min(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define travel times
travel_times = {
    ('Sunset District', 'North Beach'): 29,
    ('North Beach', 'Chinatown'): 6,
    ('Chinatown', 'Russian Hill'): 7
}

# Convert availability times to minutes
start_sunset = time_to_min("09:00")       # 540 minutes
anthony_start_avail = time_to_min("13:15") # 795 minutes
anthony_end_avail = time_to_min("14:30")   # 870 minutes
rebecca_start_avail = time_to_min("19:30") # 1170 minutes
rebecca_end_avail = time_to_min("21:15")   # 1275 minutes
melissa_end_avail = time_to_min("13:30")   # 810 minutes

# Initialize Z3 solver
s = Solver()

# Define variables for meeting times
start_M = Int('start_M')
end_M = Int('end_M')
start_A = Int('start_A')
end_A = Int('end_A')
start_R = Int('start_R')
end_R = Int('end_R')

# Constraints for Melissa
s.add(start_M == start_sunset + travel_times[('Sunset District', 'North Beach')])
s.add(end_M >= start_M + 105)
s.add(end_M <= melissa_end_avail)

# Constraints for Anthony
s.add(start_A >= end_M + travel_times[('North Beach', 'Chinatown')])
s.add(start_A >= anthony_start_avail)
s.add(end_A == start_A + 60)
s.add(end_A <= anthony_end_avail)

# Constraints for Rebecca
s.add(start_R >= end_A + travel_times[('Chinatown', 'Russian Hill')])
s.add(start_R >= rebecca_start_avail)
s.add(end_R == start_R + 105)
s.add(end_R <= rebecca_end_avail)

# Check for solution
if s.check() == sat:
    m = s.model()
    start_M_val = m[start_M].as_long()
    end_M_val = m[end_M].as_long()
    start_A_val = m[start_A].as_long()
    end_A_val = m[end_A].as_long()
    start_R_val = m[start_R].as_long()
    end_R_val = m[end_R].as_long()
    
    itinerary = [
        {"action": "meet", "person": "Melissa", "start_time": min_to_time(start_M_val), "end_time": min_to_time(end_M_val)},
        {"action": "meet", "person": "Anthony", "start_time": min_to_time(start_A_val), "end_time": min_to_time(end_A_val)},
        {"action": "meet", "person": "Rebecca", "start_time": min_to_time(start_R_val), "end_time": min_to_time(end_R_val)}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))
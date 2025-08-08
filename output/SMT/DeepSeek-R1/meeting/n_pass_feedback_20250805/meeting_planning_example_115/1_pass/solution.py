from z3 import *
import json

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Initialize Z3 solver
s = Solver()

# Define variables for meeting start times (in minutes from 9:00 AM)
carol_start = Int('carol_start')
jessica_start = Int('jessica_start')

# Convert time constraints to minutes
carol_available_start = 11 * 60 + 30  # 11:30 AM
carol_available_end = 15 * 60         # 3:00 PM
jessica_available_start = 15 * 60 + 30 # 3:30 PM
jessica_available_end = 16 * 60 + 45   # 4:45 PM

# Carol must meet for 60 minutes, so must start by carol_available_end - 60
s.add(carol_start >= carol_available_start)
s.add(carol_start <= carol_available_end - 60)

# Jessica must meet for 45 minutes, so must start by jessica_available_end - 45
s.add(jessica_start >= jessica_available_start)
s.add(jessica_start <= jessica_available_end - 45)

# Travel constraints: 
# Start at Richmond (9:00 AM = 540 minutes). Travel to Marina takes 9 minutes -> must arrive by carol_start.
# After meeting Carol (60 mins), travel to Pacific Heights takes 7 minutes -> must arrive by jessica_start.
s.add(jessica_start >= carol_start + 60 + 7)

# Check for a feasible solution
if s.check() == sat:
    m = s.model()
    carol_start_val = m.eval(carol_start).as_long()
    jessica_start_val = m.eval(jessica_start).as_long()
    
    carol_end_val = carol_start_val + 60
    jessica_end_val = jessica_start_val + 45
    
    # Convert to time strings
    carol_start_time = min_to_time(carol_start_val)
    carol_end_time = min_to_time(carol_end_val)
    jessica_start_time = min_to_time(jessica_start_val)
    jessica_end_time = min_to_time(jessica_end_val)
    
    itinerary = [
        {"action": "meet", "person": "Carol", "start_time": carol_start_time, "end_time": carol_end_time},
        {"action": "meet", "person": "Jessica", "start_time": jessica_start_time, "end_time": jessica_end_time}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))
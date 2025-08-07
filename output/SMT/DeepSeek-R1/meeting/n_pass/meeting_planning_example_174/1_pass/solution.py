from z3 import *
import json

# Define the variables
s_k = Int('s_k')   # start time of Kenneth meeting in minutes after 9:00
s_t = Int('s_t')   # start time of Thomas meeting

solver = Solver()

# Constraints for Kenneth meeting
solver.add(s_k >= 180)   # Kenneth available from 12:00 (180 minutes after 9:00)
solver.add(s_k <= 360)   # Meeting must end by 15:45 (360+45=405 minutes, which is 15:45)

# Constraints for Thomas meeting
solver.add(s_t >= s_k + 61)  # End of Kenneth meeting (s_k+45) plus travel (16 minutes)
solver.add(s_t >= 390)       # Thomas available from 15:30 (390 minutes)
solver.add(s_t <= 540)       # Meeting must end by 19:15 (540+75=615 minutes, which is 19:15)

# Check for a feasible solution
if solver.check() == sat:
    m = solver.model()
    s_k_val = m[s_k].as_long()
    s_t_val = m[s_t].as_long()
    
    # Convert minutes to time strings in "HH:MM" format
    def min_to_time(minutes):
        total_hours = 9 + (minutes // 60)
        total_minutes = minutes % 60
        return f"{total_hours:02d}:{total_minutes:02d}"
    
    k_start = min_to_time(s_k_val)
    k_end = min_to_time(s_k_val + 45)
    t_start = min_to_time(s_t_val)
    t_end = min_to_time(s_t_val + 75)
    
    # Create the itinerary
    itinerary = [
        {"action": "meet", "person": "Kenneth", "start_time": k_start, "end_time": k_end},
        {"action": "meet", "person": "Thomas", "start_time": t_start, "end_time": t_end}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')
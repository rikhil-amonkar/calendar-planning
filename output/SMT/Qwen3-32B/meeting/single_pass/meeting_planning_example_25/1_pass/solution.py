import z3
import json

solver = z3.Solver()

# Define departure time from Golden Gate Park in minutes since midnight
dep_ggp = z3.Int('dep_ggp')

# Constraints for arrival at Chinatown between 4:00 PM (960 min) and 8:00 PM (1200 min)
solver.add(dep_ggp >= 937)  # 3:37 PM = 937 minutes
solver.add(dep_ggp <= 1177) # 7:37 PM = 1177 minutes

if solver.check() == z3.sat:
    model = solver.model()
    dep_ggp_val = model[dep_ggp].as_long()
    arr_ct = dep_ggp_val + 23  # arrival at Chinatown
    
    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = to_time_str(arr_ct)
    end_time = to_time_str(arr_ct + 105)
    
    itinerary = [
        {
            "action": "meet", 
            "person": "David", 
            "start_time": start_time, 
            "end_time": end_time
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
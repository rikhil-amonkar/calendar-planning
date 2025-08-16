from z3 import *
import json

# Initialize solver
solver = Solver()

# Define variables
t1 = Int('t1')  # Start time of meeting with Emily (in minutes since midnight)

# Constraints for Emily's meeting
# Emily is available from 16:00 (960) to 17:15 (1035)
# Minimum 45 minutes meeting
solver.add(t1 >= 960)
solver.add(t1 <= 1035 - 45)  # t1 + 45 <= 1035

# Check for solution
if solver.check() == sat:
    model = solver.model()
    emily_start = model[t1].as_long()
    emily_end = emily_start + 45
    
    # Margaret's meeting starts at 19:00 (1140) and ends at 21:00 (1260)
    margaret_start = 1140
    margaret_end = 1260
    
    # Helper function to convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    # Construct itinerary
    itinerary = [
        {
            "action": "meet",
            "person": "Emily",
            "start_time": to_time_str(emily_start),
            "end_time": to_time_str(emily_end)
        },
        {
            "action": "meet",
            "person": "Margaret",
            "start_time": to_time_str(margaret_start),
            "end_time": to_time_str(margaret_end)
        }
    ]
    
    # Output JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")
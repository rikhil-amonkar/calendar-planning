from z3 import *
import json

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Create Z3 solver
solver = Solver()

# Define variables
start = Int('start')
end = Int('end')

# Timothy's availability constraints
solver.add(start >= time_to_min("20:45"))  # 20:45 PM (8:45 PM)
solver.add(end >= start + 45)              # Minimum 45 minutes meeting
solver.add(end <= time_to_min("21:30"))    # 21:30 PM (9:30 PM)

# Travel constraint: Need to arrive at Richmond District by start time
# Travel time from Alamo Square is 12 minutes
# Since arrival at Alamo Square is 9:00 AM (540 minutes), we can leave anytime after that
# The constraint is automatically satisfied since start >= 1245 (20:45) and 1245 - 12 = 1233 (20:33) > 540

# Check solution
if solver.check() == sat:
    model = solver.model()
    start_m = model[start].as_long()
    end_m = model[end].as_long()
    
    itinerary = [{
        "action": "meet",
        "person": "Timothy",
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    }]
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")
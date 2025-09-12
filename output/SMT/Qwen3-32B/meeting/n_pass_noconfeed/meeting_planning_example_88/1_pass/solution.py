import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Initialize solver
solver = z3.Solver()

# Define variables
depart_time = z3.Int('depart_time')
start_meeting = z3.Int('start_meeting')
end_meeting = z3.Int('end_meeting')

# Constraints
solver.add(depart_time >= 540)  # 9:00 AM in minutes
solver.add(start_meeting >= depart_time + 11)  # Travel time to Golden Gate Park
solver.add(start_meeting >= 1245)  # Joshua available from 8:45 PM (20:45)
solver.add(end_meeting == start_meeting + 15)  # Minimum 15-minute meeting
solver.add(end_meeting <= 1305)  # Joshua leaves at 9:45 PM (21:45)

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    s_start = model.evaluate(start_meeting).as_long()
    s_end = model.evaluate(end_meeting).as_long()
    
    itinerary = [
        {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": to_time_str(s_start),
            "end_time": to_time_str(s_end)
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
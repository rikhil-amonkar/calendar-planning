import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define variables for Emily's meeting
start_emily = z3.Int('start_emily')
end_emily = z3.Int('end_emily')

# Constraints for Emily
constraints = [
    start_emily >= 960,  # 4:00 PM
    end_emily >= start_emily + 45,  # minimum 45 min meeting
    end_emily <= 1035,  # 5:15 PM
    # After meeting Emily, travel to Russian Hill (13 min) must arrive by 1140 (7 PM)
    end_emily + 13 <= 1140
]

solver = z3.Solver()
solver.add(constraints)

if solver.check() == z3.sat:
    model = solver.model()
    start_e = model[start_emily].as_long()
    end_e = model[end_emily].as_long()

    # Margaret's meeting is fixed
    start_margaret = 1140
    end_margaret = 1260

    # Create the itinerary
    itinerary = [
        {
            "action": "meet",
            "location": "Union Square",
            "person": "Emily",
            "start_time": to_time_str(start_e),
            "end_time": to_time_str(end_e)
        },
        {
            "action": "meet",
            "location": "Russian Hill",
            "person": "Margaret",
            "start_time": to_time_str(start_margaret),
            "end_time": to_time_str(end_margaret)
        }
    ]

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))
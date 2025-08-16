import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define variables for start times (in minutes since midnight)
sk = z3.Int('sk')  # Kenneth's meeting start time
st = z3.Int('st')  # Thomas's meeting start time

# Constraints for Kenneth's meeting
solver.add(sk >= 720)  # 12:00 PM
solver.add(sk <= 900)  # 3:00 PM (to allow 45-minute meeting by 3:45 PM)

# Constraints for Thomas's meeting
solver.add(st >= 930)  # 3:30 PM
solver.add(st <= 1080) # 18:00 PM (to allow 75-minute meeting by 7:15 PM)

# Travel constraint: After meeting Kenneth, travel to Pacific Heights takes 16 minutes
# Thomas's meeting must start after arrival at Pacific Heights (sk + 45 + 16)
solver.add(st >= sk + 61)  # 45 minutes meeting + 16 minutes travel = 61

# Check if constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    sk_val = model[sk].as_long()
    st_val = model[st].as_long()

    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Build the itinerary
    itinerary = [
        {
            "action": "meet",
            "person": "Kenneth",
            "start_time": to_time_str(sk_val),
            "end_time": to_time_str(sk_val + 45)
        },
        {
            "action": "meet",
            "person": "Thomas",
            "start_time": to_time_str(st_val),
            "end_time": to_time_str(st_val + 75)
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))
import json
from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Try to meet both
solver_both = Solver()

start_r = Int('start_r')
end_r = Int('end_r')
start_c = Int('start_c')
end_c = Int('end_c')

# Constraints for meeting both
solver_both.add(start_r >= 557)  # Arrive at Union Square at 9:17 AM (557)
solver_both.add(end_r >= start_r + 120)
solver_both.add(end_r <= 780)  # Richard leaves at 1:00 PM (780)
solver_both.add(start_c >= end_r + 24)  # Travel to Presidio takes 24 min
solver_both.add(start_c >= 585)  # Charles available from 9:45 AM (585)
solver_both.add(end_c >= start_c + 120)
solver_both.add(end_c <= 780)  # Charles leaves at 1:00 PM (780)

itinerary = []

if solver_both.check() == sat:
    model = solver_both.model()
    r_start = model.evaluate(start_r).as_long()
    r_end = model.evaluate(end_r).as_long()
    c_start = model.evaluate(start_c).as_long()
    c_end = model.evaluate(end_c).as_long()
    itinerary = [
        {
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": minutes_to_time(r_start),
            "end_time": minutes_to_time(r_end)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": minutes_to_time(c_start),
            "end_time": minutes_to_time(c_end)
        }
    ]
else:
    # Try to meet Richard
    solver_r = Solver()
    solver_r.add(start_r >= 557)
    solver_r.add(end_r >= start_r + 120)
    solver_r.add(end_r <= 780)
    if solver_r.check() == sat:
        model = solver_r.model()
        r_start = model.evaluate(start_r).as_long()
        r_end = model.evaluate(end_r).as_long()
        itinerary = [
            {
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time(r_start),
                "end_time": minutes_to_time(r_end)
            }
        ]
    else:
        # Try to meet Charles
        solver_c = Solver()
        start_c = Int('start_c')
        end_c = Int('end_c')
        solver_c.add(start_c >= 585)  # Arrive at Presidio at 9:31 AM (571), but Charles starts at 9:45 AM (585)
        solver_c.add(end_c >= start_c + 120)
        solver_c.add(end_c <= 780)
        if solver_c.check() == sat:
            model = solver_c.model()
            c_start = model.evaluate(start_c).as_long()
            c_end = model.evaluate(end_c).as_long()
            itinerary = [
                {
                    "action": "meet",
                    "location": "Presidio",
                    "person": "Charles",
                    "start_time": minutes_to_time(c_start),
                    "end_time": minutes_to_time(c_end)
                }
            ]
        else:
            # No solution
            pass

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
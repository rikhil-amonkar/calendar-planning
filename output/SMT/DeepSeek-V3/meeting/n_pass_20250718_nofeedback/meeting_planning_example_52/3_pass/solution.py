from z3 import *
import json

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Variables for meeting start and end times (in minutes since midnight)
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    departure_time = Int('departure_time')  # Time you leave Russian Hill

    # Convert all times to minutes since midnight for consistency
    arrival_at_russian_hill = 9 * 60  # 9:00 AM
    barbara_start = 13 * 60 + 15      # 1:15 PM
    barbara_end = 18 * 60 + 15        # 6:15 PM
    travel_time = 14                  # 14 minutes to Richmond District

    # Constraints
    s.add(departure_time >= arrival_at_russian_hill)  # Can't leave before arriving
    s.add(meet_start == departure_time + travel_time) # Arrival at Richmond District
    s.add(meet_start >= barbara_start)               # Can't meet before Barbara is available
    s.add(meet_end == meet_start + 45)               # Meeting duration
    s.add(meet_end <= barbara_end)                   # Can't meet after Barbara leaves

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        end = m[meet_end].as_long()
        depart = m[departure_time].as_long()

        # Convert back to HH:MM format
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        solution = {
            "itinerary": [
                {
                    "action": "travel",
                    "from": "Russian Hill",
                    "to": "Richmond District",
                    "start_time": to_time_str(depart),
                    "end_time": to_time_str(depart + travel_time)
                },
                {
                    "action": "meet",
                    "person": "Barbara",
                    "start_time": to_time_str(start),
                    "end_time": to_time_str(end)
                }
            ]
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

solve_scheduling()
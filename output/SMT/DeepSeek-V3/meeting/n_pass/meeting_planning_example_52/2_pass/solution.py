from z3 import *
import json

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Variables for meeting start and end times (in minutes since 9:00 AM)
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')

    # Convert times to minutes since 9:00 AM
    barbara_start = (13 * 60 + 15) - (9 * 60)  # 1:15 PM is 255 minutes after 9:00 AM
    barbara_end = (18 * 60 + 15) - (9 * 60)    # 6:15 PM is 555 minutes after 9:00 AM
    travel_time = 14                            # 14 minutes to Richmond District

    # Constraints
    s.add(meet_start >= barbara_start)          # Cannot start before Barbara is available
    s.add(meet_end <= barbara_end)              # Cannot end after Barbara leaves
    s.add(meet_end == meet_start + 45)          # Meeting lasts 45 minutes
    s.add(meet_start >= travel_time)            # Must account for travel time (leave Russian Hill at meet_start - travel_time)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        end = m[meet_end].as_long()

        # Convert back to HH:MM format
        def to_time_str(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_time = to_time_str(start)
        end_time = to_time_str(end)

        solution = {
            "itinerary": [
                {"action": "meet", "person": "Barbara", "start_time": start_time, "end_time": end_time}
            ]
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

solve_scheduling()
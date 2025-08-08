from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer (not Solver, since we need minimization)
    opt = Optimize()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Convert time constraints to minutes since 9:00 AM
    kenneth_available_start = (14 * 60 + 15) - (9 * 60)  # 2:15 PM is 14:15, 9:00 AM is 9:00
    kenneth_available_end = (19 * 60 + 45) - (9 * 60)     # 7:45 PM is 19:45
    travel_time = 11  # minutes

    # Constraints:
    # 1. Meeting must start after Kenneth is available (2:15 PM)
    opt.add(start_time >= kenneth_available_start)
    # 2. Meeting must end before Kenneth leaves (7:45 PM)
    opt.add(end_time <= kenneth_available_end)
    # 3. Meeting duration is at least 90 minutes
    opt.add(end_time - start_time >= 90)
    # 4. You must leave Fisherman's Wharf 11 minutes before the meeting starts
    opt.add(start_time - travel_time >= 0)  # Leave time cannot be before 9:00 AM

    # Optimize for the earliest possible meeting (minimize start_time)
    opt.minimize(start_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        # Convert minutes back to HH:MM format
        def to_time_str(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = to_time_str(start)
        end_str = to_time_str(end)

        # Prepare the itinerary
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Kenneth",
                    "start_time": start_str,
                    "end_time": end_str
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))
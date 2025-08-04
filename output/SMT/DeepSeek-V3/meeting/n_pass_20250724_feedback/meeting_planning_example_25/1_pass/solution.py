from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for the start and end times of the meeting with David
    # Times are represented in minutes since 9:00 AM (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Constraints:
    # 1. David is available from 4:00 PM (1020 minutes since midnight) to 9:45 PM (1305 minutes since midnight)
    # 2. Meeting duration is at least 105 minutes
    # 3. Travel time from Golden Gate Park to Chinatown is 23 minutes
    # 4. You arrive at Golden Gate Park at 9:00 AM (540 minutes since midnight)

    # Convert times to minutes since midnight for easier arithmetic
    david_available_start = 16 * 60  # 4:00 PM
    david_available_end = 21 * 60 + 45  # 9:45 PM
    travel_time = 23
    arrival_at_park = 9 * 60  # 9:00 AM

    # You can leave Golden Gate Park at any time after arrival (9:00 AM)
    # The earliest you can arrive at Chinatown is arrival_at_park + travel_time
    # But David is only available from david_available_start
    # So the meeting must start >= david_available_start and end <= david_available_end
    s.add(start_time >= david_available_start)
    s.add(end_time <= david_available_end)
    s.add(end_time - start_time >= 105)  # Meeting duration >= 105 minutes

    # The time to leave Golden Gate Park is start_time - travel_time
    # You must leave after arriving at Golden Gate Park (arrival_at_park)
    s.add(start_time - travel_time >= arrival_at_park)

    # Optimize to find the earliest possible meeting time
    # This is just to find a feasible solution, not necessarily the earliest
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        # Convert minutes back to HH:MM format
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_str = to_time_str(start)
        end_str = to_time_str(end)

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "David",
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
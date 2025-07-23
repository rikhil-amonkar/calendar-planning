from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    start = Int('start')
    end = Int('end')

    # Kenneth's availability in minutes since 9:00 AM
    # Kenneth is available from 2:15 PM (315 minutes from 9:00 AM) to 7:45 PM (645 minutes from 9:00 AM)
    kenneth_start = 315  # 2:15 PM
    kenneth_end = 645    # 7:45 PM

    # Travel time is 11 minutes
    travel_time = 11

    # Constraints:
    # 1. Meeting must be within Kenneth's availability
    s.add(start >= kenneth_start)
    s.add(end <= kenneth_end)

    # 2. Meeting duration must be at least 90 minutes
    s.add(end - start >= 90)

    # 3. You start at Fisherman's Wharf at 9:00 AM (0 minutes), so you can leave after accounting for travel time
    # Since you can leave anytime before the meeting starts, but the earliest you can arrive at Nob Hill is 9:11 AM,
    # but Kenneth is only available from 2:15 PM, so this constraint is already covered by the first constraint.

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start_time = m[start].as_long()
        end_time = m[end].as_long()

        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = (minutes // 60) % 24
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)

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
        print(json.dumps(itinerary, indent=2))
    else:
        print("No valid schedule found.")

solve_scheduling()
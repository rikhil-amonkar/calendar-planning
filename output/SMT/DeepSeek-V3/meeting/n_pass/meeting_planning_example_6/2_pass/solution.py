from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    start = Int('start')
    end = Int('end')

    # Kenneth's availability in minutes since 9:00 AM
    kenneth_start = 315  # 2:15 PM
    kenneth_end = 645    # 7:45 PM

    # Travel time is 11 minutes (but not directly relevant for meeting time constraints)
    travel_time = 11

    # Constraints:
    # 1. Meeting must start within Kenneth's availability
    s.add(start >= kenneth_start)
    # 2. Meeting must end within Kenneth's availability
    s.add(end <= kenneth_end)
    # 3. Meeting duration must be at least 90 minutes
    s.add(end - start >= 90)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start_time = m[start].as_long()
        end_time = m[end].as_long()

        # Convert minutes since 9:00 AM to 24-hour time format
        def minutes_to_time(minutes):
            total_minutes = 9 * 60 + minutes  # 9:00 AM + minutes
            hours = (total_minutes // 60) % 24
            mins = total_minutes % 60
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
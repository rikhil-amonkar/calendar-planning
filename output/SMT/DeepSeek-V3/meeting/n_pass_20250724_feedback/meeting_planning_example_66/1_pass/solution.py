from z3 import *
import json

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    start = Int('start')
    end = Int('end')

    # Constraints
    # Robert is available from 11:15 AM (135 minutes after 9:00 AM) to 5:45 PM (525 minutes after 9:00 AM)
    s.add(start >= 135)  # 11:15 AM is 135 minutes after 9:00 AM
    s.add(end <= 525)    # 5:45 PM is 525 minutes after 9:00 AM
    s.add(end - start >= 120)  # Meeting duration >= 120 minutes

    # Travel time from Nob Hill to Presidio is 17 minutes
    # You arrive at Nob Hill at 9:00 AM, so earliest you can be at Presidio is 9:17 AM (17 minutes after 9:00 AM)
    # But since Robert is only available from 11:15 AM, this is already covered by start >= 135

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start_time = m[start].as_long()
        end_time = m[end].as_long()

        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours + 9:02d}:{mins:02d}"  # Since we started counting from 9:00 AM

        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Robert",
                    "start_time": start_str,
                    "end_time": end_str
                }
            ]
        }
        print(json.dumps(itinerary, indent=2))
    else:
        print("No valid schedule found.")

solve_scheduling()
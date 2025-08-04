from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for the meeting start and end times with Joshua
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')

    # Convert times to minutes since 9:00 AM (540 minutes)
    # Joshua's availability: 8:45 PM (20:45) to 9:45 PM (21:45) -> 1245 to 1305 minutes since midnight
    # Since we start at 9:00 AM (540 minutes), we adjust Joshua's window to be 1245 - 540 = 705 to 1305 - 540 = 765 minutes since 9:00 AM

    # Constraints:
    # 1. Meeting must be within Joshua's availability (705 to 765 minutes since 9:00 AM)
    s.add(meet_start >= 705)
    s.add(meet_end <= 765)
    # 2. Meeting duration is at least 15 minutes
    s.add(meet_end - meet_start >= 15)
    # 3. Travel time to Golden Gate Park is 11 minutes, so you must leave Sunset District at meet_start - 11
    leave_sunset = meet_start - 11
    s.add(leave_sunset >= 0)  # Cannot leave before 9:00 AM (0 minutes since 9:00 AM)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        end = m[meet_end].as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)

        # Prepare the itinerary
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Joshua",
                    "start_time": start_time,
                    "end_time": end_time
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve the problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))
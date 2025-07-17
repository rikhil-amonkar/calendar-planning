from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Variables
    meet_start = Int('meet_start')  # in minutes since 9:00 AM
    meet_duration = Int('meet_duration')  # in minutes

    # Constraints
    s.add(meet_duration >= 15)  # minimum meeting duration
    s.add(meet_start >= 0)  # cannot start before 9:00 AM

    # Joshua's availability: 8:45 PM (20:45) to 9:45 PM (21:45)
    # Convert to minutes since 9:00 AM: 11 hours 45 minutes = 705 minutes
    joshua_start = 11 * 60 + 45  # 705 minutes
    joshua_end = 12 * 60 + 45     # 765 minutes

    # Meeting must be within Joshua's availability
    s.add(meet_start >= joshua_start)
    s.add(meet_start + meet_duration <= joshua_end)

    # Travel constraints
    # You can leave Sunset District at meet_start - 11 to arrive at Golden Gate Park by meet_start
    s.add(meet_start - 11 >= 0)  # cannot leave before 9:00 AM

    # After meeting, you can return to Sunset District by meet_start + meet_duration + 10
    # No constraint on return time since the day ends after meeting Joshua

    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        duration = m[meet_duration].as_long()

        # Convert minutes to HH:MM format
        start_hour = 9 + start // 60
        start_minute = start % 60
        end_hour = 9 + (start + duration) // 60
        end_minute = (start + duration) % 60

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Joshua",
                    "start_time": f"{start_hour:02d}:{start_minute:02d}",
                    "end_time": f"{end_hour:02d}:{end_minute:02d}"
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))
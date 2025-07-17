from z3 import *
import json

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    meet_start = Int('meet_start')  # in minutes from 9:00 AM
    meet_duration = Int('meet_duration')

    # Constraints
    # Robert's availability: 11:15 AM to 5:45 PM (135 to 525 minutes from 9:00 AM)
    s.add(meet_start >= 135)  # 11:15 AM is 135 minutes after 9:00 AM
    s.add(meet_start + meet_duration <= 525)  # 5:45 PM is 525 minutes after 9:00 AM
    s.add(meet_duration >= 120)  # Minimum meeting duration

    # Travel time: 17 minutes to Presidio
    s.add(meet_start >= 17)  # Must have time to travel from Nob Hill to Presidio

    # Maximize meeting duration (optional, but here we set it to exactly 120)
    s.add(meet_duration == 120)

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        duration = m[meet_duration].as_long()

        # Convert minutes to HH:MM format
        start_hour = 9 + (start // 60)
        start_min = start % 60
        end_hour = 9 + ((start + duration) // 60)
        end_min = (start + duration) % 60

        start_time = f"{start_hour:02d}:{start_min:02d}"
        end_time = f"{end_hour:02d}:{end_min:02d}"

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Robert",
                    "start_time": start_time,
                    "end_time": end_time
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))
from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables
    meet_start = Int('meet_start')  # Minutes since 9:00 AM
    meet_duration = Int('meet_duration')

    # Constraints
    # Robert is available from 11:15 AM to 5:45 PM (135 to 525 minutes since 9:00 AM)
    robert_start = 135  # 11:15 AM is 135 minutes after 9:00 AM
    robert_end = 525    # 5:45 PM is 525 minutes after 9:00 AM

    # Travel times
    travel_to_presidio = 17
    travel_from_presidio = 18

    # You arrive at Nob Hill at 9:00 AM (time 0)
    # You must leave Nob Hill at least 17 minutes before meeting starts
    s.add(meet_start >= travel_to_presidio)
    # Meeting must start during Robert's availability
    s.add(meet_start >= robert_start)
    s.add(meet_start + meet_duration <= robert_end)
    # Meeting duration must be at least 120 minutes
    s.add(meet_duration >= 120)
    # You must return to Nob Hill by some time (not explicitly constrained, but we can ignore for this problem)

    # Optimize for earliest meeting start to free up the rest of the day
    s.minimize(meet_start)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        duration = m[meet_duration].as_long()

        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours + 9:02d}:{mins:02d}"  # Since 0 is 9:00 AM

        start_time = minutes_to_time(start)
        end_time = minutes_to_time(start + duration)

        # Create itinerary
        itinerary = [{
            "action": "meet",
            "person": "Robert",
            "start_time": start_time,
            "end_time": end_time
        }]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))
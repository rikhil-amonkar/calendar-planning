from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables (in minutes since 9:00 AM)
    meet_kenneth_start = Int('meet_kenneth_start')
    meet_kenneth_end = Int('meet_kenneth_end')

    # Convert time constraints to minutes since 9:00 AM (540 minutes)
    kenneth_available_start = (14 * 60 + 15) - 540  # 2:15 PM is 14:15 (855 - 540 = 315)
    kenneth_available_end = (19 * 60 + 45) - 540    # 7:45 PM is 19:45 (1185 - 540 = 645)
    min_meet_duration = 90
    travel_time = 11  # minutes to Nob Hill

    # Constraints
    # 1. Meeting must start after Kenneth becomes available (accounting for travel time)
    s.add(meet_kenneth_start >= kenneth_available_start)
    # 2. Meeting must end before Kenneth leaves
    s.add(meet_kenneth_end <= kenneth_available_end)
    # 3. Meeting duration must be at least 90 minutes
    s.add(meet_kenneth_end - meet_kenneth_start >= min_meet_duration)
    # 4. Must have time to travel to Nob Hill before meeting starts
    # (since we start at Fisherman's Wharf at 9:00 AM, we can leave anytime before)
    # No constraint needed here since we have all day before 2:15 PM to travel

    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        start = m[meet_kenneth_start].as_long()
        end = m[meet_kenneth_end].as_long()

        # Convert back to HH:MM format
        base_time = datetime.datetime(2023, 1, 1, 9, 0)  # Starting at 9:00 AM
        start_time = base_time + datetime.timedelta(minutes=start)
        end_time = base_time + datetime.timedelta(minutes=end)

        itinerary = [{
            "action": "meet",
            "person": "Kenneth",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        }]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
solution = solve_scheduling()
print(solution)
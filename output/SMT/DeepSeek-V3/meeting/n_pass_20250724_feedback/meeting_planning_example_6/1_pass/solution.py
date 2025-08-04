from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables
    meet_kenneth_start = Int('meet_kenneth_start')
    meet_kenneth_end = Int('meet_kenneth_end')

    # Convert time to minutes since 9:00 AM (540 minutes)
    kenneth_available_start = (14 * 60 + 15) - 540  # 2:15 PM is 14:15
    kenneth_available_end = (19 * 60 + 45) - 540    # 7:45 PM is 19:45
    min_meet_duration = 90

    # Constraints
    s.add(meet_kenneth_start >= kenneth_available_start)
    s.add(meet_kenneth_end <= kenneth_available_end)
    s.add(meet_kenneth_end - meet_kenneth_start >= min_meet_duration)
    s.add(meet_kenneth_start + 11 <= meet_kenneth_start)  # Travel time is already accounted for in the schedule

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
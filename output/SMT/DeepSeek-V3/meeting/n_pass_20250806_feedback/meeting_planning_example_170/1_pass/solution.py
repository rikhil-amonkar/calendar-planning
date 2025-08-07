from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times
    emily_start = Int('emily_start')  # in minutes from 9:00 AM
    emily_end = Int('emily_end')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Convert time constraints to minutes from 9:00 AM (540 minutes)
    # Emily's availability: 4:00 PM to 5:15 PM is 16:00 to 17:15, which is 960 to 1035 minutes from midnight
    # From 9:00 AM (540 minutes from midnight), so 960-540 = 420 to 1035-540 = 495 minutes from 9:00 AM
    emily_min_start = 420  # 4:00 PM is 7 hours after 9:00 AM (7*60=420)
    emily_max_end = 495    # 5:15 PM is 8 hours and 15 minutes after 9:00 AM (8*60 +15=495)
    emily_duration = 45    # minimum 45 minutes

    # Margaret's availability: 7:00 PM to 9:00 PM is 19:00 to 21:00, which is 1140 to 1260 minutes from midnight
    # From 9:00 AM (540 minutes), so 1140-540 = 600 to 1260-540 = 720 minutes from 9:00 AM
    margaret_min_start = 600  # 7:00 PM is 10 hours after 9:00 AM (10*60=600)
    margaret_max_end = 720     # 9:00 PM is 12 hours after 9:00 AM (12*60=720)
    margaret_duration = 120    # minimum 120 minutes

    # Add constraints for Emily's meeting
    s.add(emily_start >= emily_min_start)
    s.add(emily_end <= emily_max_end)
    s.add(emily_end == emily_start + emily_duration)

    # Add constraints for Margaret's meeting
    s.add(margaret_start >= margaret_min_start)
    s.add(margaret_end <= margaret_max_end)
    s.add(margaret_end == margaret_start + margaret_duration)

    # Travel times (in minutes)
    # From North Beach to Union Square: 7
    # From Union Square to Russian Hill: 13
    # From Russian Hill to North Beach: 5
    # Initial location: North Beach at time 0 (9:00 AM)

    # To meet Emily at Union Square, must travel from North Beach to Union Square (7 minutes)
    # So, emily_start >= 7 (since we start at North Beach at time 0)
    s.add(emily_start >= 7)

    # After meeting Emily, to meet Margaret at Russian Hill, must travel from Union Square to Russian Hill (13 minutes)
    # So, margaret_start >= emily_end + 13
    s.add(margaret_start >= emily_end + 13)

    # After meeting Margaret, return to North Beach (5 minutes) - but this isn't a constraint for meeting friends

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Extract the values
        emily_start_val = m[emily_start].as_long()
        emily_end_val = m[emily_end].as_long()
        margaret_start_val = m[margaret_start].as_long()
        margaret_end_val = m[margaret_end].as_long()

        # Convert minutes from 9:00 AM back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes from midnight
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        emily_start_time = minutes_to_time(emily_start_val)
        emily_end_time = minutes_to_time(emily_end_val)
        margaret_start_time = minutes_to_time(margaret_start_val)
        margaret_end_time = minutes_to_time(margaret_end_val)

        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": emily_start_time, "end_time": emily_end_time},
            {"action": "meet", "person": "Margaret", "start_time": margaret_start_time, "end_time": margaret_end_time}
        ]

        # Return as JSON
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))
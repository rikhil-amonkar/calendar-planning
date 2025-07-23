from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define time variables in minutes since 9:00 AM (0 minutes)
    meet_melissa_start = Int('meet_melissa_start')
    meet_melissa_end = Int('meet_melissa_end')
    meet_nancy_start = Int('meet_nancy_start')
    meet_nancy_end = Int('meet_nancy_end')
    meet_emily_start = Int('meet_emily_start')
    meet_emily_end = Int('meet_emily_end')

    # Travel times (in minutes)
    travel_to_melissa = 25  # Fisherman's Wharf to Golden Gate Park
    travel_melissa_to_emily = 7  # Golden Gate Park to Richmond District
    travel_emily_to_nancy = 7  # Richmond District to Presidio

    # Constraints

    # 1. Start at Fisherman's Wharf at 9:00 AM (0 minutes)
    # Travel to Melissa (Golden Gate Park) takes 25 minutes
    s.add(meet_melissa_start >= travel_to_melissa)
    s.add(meet_melissa_end == meet_melissa_start + 15)  # Meet Melissa for 15 minutes

    # Melissa's availability: 8:30 AM (-30 minutes) to 8:00 PM (660 minutes)
    s.add(meet_melissa_start >= -30)
    s.add(meet_melissa_end <= 660)

    # 2. Travel from Melissa to Emily: starts after meeting Melissa, takes 7 minutes
    travel_to_emily_start = meet_melissa_end
    travel_to_emily_end = travel_to_emily_start + travel_melissa_to_emily
    meet_emily_start = travel_to_emily_end
    s.add(meet_emily_end == meet_emily_start + 120)  # Meet Emily for 120 minutes

    # Emily's availability: 4:45 PM (510 minutes) to 10:00 PM (780 minutes)
    s.add(meet_emily_start >= 510)
    s.add(meet_emily_end <= 780)

    # 3. Travel from Emily to Nancy: starts after meeting Emily, takes 7 minutes
    travel_to_nancy_start = meet_emily_end
    travel_to_nancy_end = travel_to_nancy_start + travel_emily_to_nancy
    meet_nancy_start = travel_to_nancy_end
    s.add(meet_nancy_end == meet_nancy_start + 105)  # Meet Nancy for 105 minutes

    # Nancy's availability: 7:45 PM (630 minutes) to 10:00 PM (780 minutes)
    s.add(meet_nancy_start >= 630)
    s.add(meet_nancy_end <= 780)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        # Melissa's meeting
        melissa_start = m.eval(meet_melissa_start).as_long()
        melissa_end = m.eval(meet_melissa_end).as_long()
        # Emily's meeting
        emily_start = m.eval(meet_emily_start).as_long()
        emily_end = m.eval(meet_emily_end).as_long()
        # Nancy's meeting
        nancy_start = m.eval(meet_nancy_start).as_long()
        nancy_end = m.eval(meet_nancy_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": minutes_to_time(melissa_start), "end_time": minutes_to_time(melissa_end)},
            {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_start), "end_time": minutes_to_time(emily_end)},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(nancy_start), "end_time": minutes_to_time(nancy_end)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))
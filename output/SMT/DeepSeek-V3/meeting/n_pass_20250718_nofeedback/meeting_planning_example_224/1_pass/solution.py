from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Time variables in minutes since 9:00 AM (0 minutes)
    meet_melissa_start = Int('meet_melissa_start')
    meet_melissa_end = Int('meet_melissa_end')
    meet_emily_start = Int('meet_emily_start')
    meet_emily_end = Int('meet_emily_end')
    meet_nancy_start = Int('meet_nancy_start')
    meet_nancy_end = Int('meet_nancy_end')

    # Travel times
    # Fisherman's Wharf to Golden Gate Park: 25 minutes
    s.add(meet_melissa_start >= 25)
    s.add(meet_melissa_end == meet_melissa_start + 15)
    # Melissa's availability: 8:30 AM (-30 minutes) to 8:00 PM (660 minutes)
    s.add(meet_melissa_start >= -30)
    s.add(meet_melissa_end <= 660)

    # Travel from Golden Gate Park to Richmond District: 7 minutes
    # Emily's availability starts at 4:45 PM (510 minutes)
    # So leave Golden Gate Park at 510 - 7 = 503 minutes
    travel_to_emily_start = meet_melissa_end  # after meeting Melissa
    s.add(travel_to_emily_start <= 503)  # must leave by 503 minutes to arrive at 510
    meet_emily_start = 510  # 4:45 PM
    meet_emily_end = meet_emily_start + 120  # 6:45 PM
    s.add(meet_emily_end <= 780)  # Emily's availability ends at 10:00 PM (780 minutes)

    # Travel from Richmond District to Presidio: 7 minutes
    travel_to_nancy_start = meet_emily_end
    travel_to_nancy_end = travel_to_nancy_start + 7
    meet_nancy_start = 630  # 7:45 PM
    s.add(travel_to_nancy_end <= 630)  # must arrive by 7:45 PM
    meet_nancy_end = meet_nancy_start + 105  # 9:30 PM
    s.add(meet_nancy_end <= 780)  # Nancy's availability ends at 10:00 PM

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        # Melissa's meeting
        melissa_start = m.eval(meet_melissa_start).as_long()
        melissa_end = m.eval(meet_melissa_end).as_long()
        # Emily's meeting is fixed
        emily_start = 510
        emily_end = 630
        # Nancy's meeting is fixed
        nancy_start = 630
        nancy_end = 735

        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": minutes_to_time(melissa_start), "end_time": minutes_to_time(melissa_end)},
            {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_start), "end_time": minutes_to_time(emily_end)},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(nancy_start), "end_time": minutes_to_time(nancy_end)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))
from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Variables for meeting start and end times
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Convert times to minutes since 9:00 AM (540 minutes)
    emily_available_start = 16 * 60  # 4:00 PM
    emily_available_end = 17 * 60 + 15  # 5:15 PM
    margaret_available_start = 19 * 60  # 7:00 PM
    margaret_available_end = 21 * 60  # 9:00 PM

    # Constraints for Emily
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)
    s.add(emily_end - emily_start >= 45)  # Minimum 45 minutes

    # Constraints for Margaret
    s.add(margaret_start >= margaret_available_start)
    s.add(margaret_end <= margaret_available_end)
    s.add(margaret_end - margaret_start >= 120)  # Minimum 120 minutes

    # Travel constraints
    # Start at North Beach at 9:00 AM (540 minutes)
    # Travel to Union Square: 7 minutes
    s.add(emily_start >= 540 + 7)

    # Travel from Union Square to Russian Hill: 13 minutes
    s.add(margaret_start >= emily_end + 13)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        emily_start_min = m[emily_start].as_long()
        emily_end_min = m[emily_end].as_long()
        margaret_start_min = m[margaret_start].as_long()
        margaret_end_min = m[margaret_end].as_long()

        # Convert minutes back to HH:MM format
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": to_time_str(emily_start_min), "end_time": to_time_str(emily_end_min)},
            {"action": "meet", "person": "Margaret", "start_time": to_time_str(margaret_start_min), "end_time": to_time_str(margaret_end_min)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Print the solution
import json
print(json.dumps(solve_scheduling(), indent=2))
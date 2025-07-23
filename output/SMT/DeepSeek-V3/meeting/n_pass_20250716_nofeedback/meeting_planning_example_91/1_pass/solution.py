from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Variables for meeting Daniel
    meet_daniel_start = Int('meet_daniel_start')
    meet_daniel_end = Int('meet_daniel_end')

    # Constraints for Daniel's availability (7:00 PM to 8:15 PM)
    # Convert times to minutes since 9:00 AM (540 minutes)
    daniel_available_start = (19 * 60) - 540  # 7:00 PM is 19:00 in 24-hour format
    daniel_available_end = (20 * 60 + 15) - 540  # 8:15 PM is 20:15

    # Meeting must be within Daniel's availability
    s.add(meet_daniel_start >= daniel_available_start)
    s.add(meet_daniel_end <= daniel_available_end)
    s.add(meet_daniel_end - meet_daniel_start >= 75)  # Minimum 75 minutes

    # Travel time constraints (14 minutes to Richmond District)
    # You must leave Russian Hill at least 14 minutes before meeting Daniel
    leave_russian_hill = Int('leave_russian_hill')
    s.add(leave_russian_hill + 14 <= meet_daniel_start)
    s.add(leave_russian_hill >= 0)  # Cannot leave before 9:00 AM

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            h = (total_minutes // 60) % 24
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        meet_start = m[meet_daniel_start].as_long()
        meet_end = m[meet_daniel_end].as_long()
        itinerary = [
            {
                "action": "meet",
                "person": "Daniel",
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            }
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))
from z3 import *
import json

def solve_scheduling():
    # Create optimizer instance instead of solver
    opt = Optimize()

    # All times in minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM
    barbara_start = 13 * 60 + 15  # 1:15 PM
    barbara_end = 18 * 60 + 15    # 6:15 PM
    travel_duration = 14           # 14 minutes
    min_meeting = 45              # 45 minutes

    # Decision variables
    departure = Int('departure')  # When you leave Russian Hill
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Constraints
    opt.add(departure >= arrival_time)  # Can't leave before arriving
    opt.add(meeting_start == departure + travel_duration)  # Arrival time
    opt.add(meeting_start >= barbara_start)  # Can't meet before available
    opt.add(meeting_end == meeting_start + min_meeting)  # Meeting duration
    opt.add(meeting_end <= barbara_end)  # Must finish by 6:15 PM

    # Find earliest possible meeting
    opt.minimize(meeting_start)
    
    if opt.check() == sat:
        m = opt.model()
        depart = m[departure].as_long()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()

        def format_time(minutes):
            return f"{minutes//60:02d}:{minutes%60:02d}"

        solution = {
            "itinerary": [
                {
                    "action": "travel",
                    "from": "Russian Hill",
                    "to": "Richmond District",
                    "start_time": format_time(depart),
                    "end_time": format_time(depart + travel_duration)
                },
                {
                    "action": "meet",
                    "person": "Barbara",
                    "start_time": format_time(start),
                    "end_time": format_time(end)
                }
            ]
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No valid schedule found")

solve_scheduling()
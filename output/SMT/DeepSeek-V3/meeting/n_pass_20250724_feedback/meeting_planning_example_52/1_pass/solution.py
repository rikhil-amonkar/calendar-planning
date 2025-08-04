from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for the start and end times of the meeting with Barbara
    # We'll represent times as integers (minutes since 9:00 AM)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Constraints:
    # 1. You arrive at Russian Hill at 9:00 AM (time = 0 minutes)
    # 2. Travel to Richmond District takes 14 minutes, so earliest arrival is 14 minutes
    # 3. Barbara is available from 1:15 PM to 6:15 PM (255 to 495 minutes since 9:00 AM)
    # 4. Meeting duration is at least 45 minutes
    # 5. Meeting must be within Barbara's availability

    # Convert Barbara's availability to minutes since 9:00 AM
    barbara_start = (13 * 60 + 15) - (9 * 60)  # 1:15 PM is 255 minutes
    barbara_end = (18 * 60 + 15) - (9 * 60)    # 6:15 PM is 495 minutes

    # Add constraints
    s.add(start_time >= 14)  # Earliest you can arrive at Richmond District
    s.add(start_time >= barbara_start)  # Meeting must start during Barbara's availability
    s.add(end_time <= barbara_end)      # Meeting must end during Barbara's availability
    s.add(end_time == start_time + 45)  # Meeting duration is exactly 45 minutes

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        start = m.eval(start_time).as_long()
        end = m.eval(end_time).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_hours = 9 + minutes // 60
            total_minutes = minutes % 60
            return f"{total_hours:02d}:{total_minutes:02d}"

        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)

        # Prepare the itinerary
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Barbara",
                    "start_time": start_str,
                    "end_time": end_str
                }
            ]
        }
        print(json.dumps(itinerary, indent=2))
    else:
        print("No feasible schedule found.")

solve_scheduling()
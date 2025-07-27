from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Constraints:
    # 1. You arrive at Alamo Square at 9:00 AM (time = 0 minutes)
    # 2. Timothy is available from 20:45 to 21:30 (11 hours and 45 minutes to 12 hours and 30 minutes since 9:00 AM)
    timothy_start = 11 * 60 + 45  # 20:45 is 11 hours and 45 minutes after 9:00 AM
    timothy_end = 12 * 60 + 30    # 21:30 is 12 hours and 30 minutes after 9:00 AM

    # 3. Meeting duration is at least 45 minutes
    s.add(end_time - start_time >= 45)

    # 4. Meeting must be within Timothy's availability
    s.add(start_time >= timothy_start)
    s.add(end_time <= timothy_end)

    # 5. Travel time to Richmond District is 12 minutes
    # Since you start at Alamo Square at time 0, you can leave anytime after 0 to reach Richmond District
    # The meeting must start at least 12 minutes after you leave Alamo Square
    # But since Timothy's availability is late, this doesn't add any new constraints

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        # Convert minutes to HH:MM format
        base_time = datetime.datetime(2023, 1, 1, 9, 0)  # 9:00 AM
        start_time_str = (base_time + datetime.timedelta(minutes=start)).strftime("%H:%M")
        end_time_str = (base_time + datetime.timedelta(minutes=end)).strftime("%H:%M")

        return {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Timothy",
                    "start_time": start_time_str,
                    "end_time": end_time_str
                }
            ]
        }
    else:
        return {"itinerary": []}

# Print the solution
print(solve_scheduling())
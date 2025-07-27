from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')

    # Daniel's availability: 7:00 PM (19:00) to 8:15 PM (20:15) is 1140 to 1215 minutes since midnight
    # Since we arrive at Russian Hill at 9:00 AM (540 minutes since midnight), we calculate relative to that
    daniel_start = (19 * 60) - 540  # 7:00 PM is 1140 minutes since midnight, so 1140 - 540 = 600 minutes since 9:00 AM
    daniel_end = (20 * 60 + 15) - 540  # 8:15 PM is 1215 minutes since midnight, so 1215 - 540 = 675 minutes since 9:00 AM

    # Constraints:
    # 1. Meeting must start and end within Daniel's availability
    s.add(meet_start >= daniel_start)
    s.add(meet_end <= daniel_end)
    # 2. Meeting duration is at least 75 minutes
    s.add(meet_end - meet_start >= 75)
    # 3. Travel time to Richmond District is 14 minutes
    #    So departure from Russian Hill is meet_start - 14
    departure = meet_start - 14
    s.add(departure >= 0)  # Cannot depart before 9:00 AM (0 minutes since 9:00 AM)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        end = m[meet_end].as_long()

        # Convert minutes back to HH:MM format
        def to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            hh = (total_minutes // 60) % 24
            mm = total_minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_time = to_time(start)
        end_time = to_time(end)

        # Return the itinerary
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Daniel",
                    "start_time": start_time,
                    "end_time": end_time
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve and print the result
print(solve_scheduling())
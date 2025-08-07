from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')

    # Jeffrey at Union Square: 3:00PM (360 mins) to 10:00PM (780 mins), min 75 mins
    s.add(jeffrey_start >= 360, jeffrey_end <= 780)
    s.add(jeffrey_end - jeffrey_start >= 75)

    # Sarah at North Beach: 4:00PM (420 mins) to 6:15PM (555 mins), min 60 mins
    s.add(sarah_start >= 420, sarah_end <= 555)
    s.add(sarah_end - sarah_start >= 60)

    # Travel times (in minutes)
    sunset_to_union = 30  # Sunset District to Union Square
    union_to_north = 10   # Union Square to North Beach

    # Starting at Sunset District at 9:00 AM (0 mins)
    # First meeting: Jeffrey at Union Square
    s.add(jeffrey_start >= sunset_to_union)

    # After Jeffrey, travel to North Beach for Sarah
    s.add(sarah_start >= jeffrey_end + union_to_north)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def to_time(minutes):
            hours = 9 + (minutes // 60)
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        jeffrey_s = m.eval(jeffrey_start).as_long()
        jeffrey_e = m.eval(jeffrey_end).as_long()
        sarah_s = m.eval(sarah_start).as_long()
        sarah_e = m.eval(sarah_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Jeffrey", "start_time": to_time(jeffrey_s), "end_time": to_time(jeffrey_e)},
            {"action": "meet", "person": "Sarah", "start_time": to_time(sarah_s), "end_time": to_time(sarah_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Print the solution
print(json.dumps(solve_scheduling(), indent=2))
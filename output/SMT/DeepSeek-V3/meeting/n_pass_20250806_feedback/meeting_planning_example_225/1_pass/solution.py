from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times
    # Jeffrey at Union Square: 3:00PM to 10:00PM, min 75 mins
    jeffrey_start = Int('jeffrey_start')  # in minutes from 9:00AM
    jeffrey_end = Int('jeffrey_end')

    # Brian at Alamo Square: 4:00PM to 5:30PM, min 75 mins
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Sarah at North Beach: 4:00PM to 6:15PM, min 60 mins
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')

    # Convert all times to minutes since 9:00AM
    # Jeffrey's window: 3:00PM (360 mins) to 10:00PM (780 mins)
    s.add(jeffrey_start >= 360, jeffrey_end <= 780)
    s.add(jeffrey_end - jeffrey_start >= 75)

    # Brian's window: 4:00PM (420 mins) to 5:30PM (510 mins)
    s.add(brian_start >= 420, brian_end <= 510)
    s.add(brian_end - brian_start >= 75)

    # Sarah's window: 4:00PM (420 mins) to 6:15PM (555 mins)
    s.add(sarah_start >= 420, sarah_end <= 555)
    s.add(sarah_end - sarah_start >= 60)

    # Travel times:
    # Sunset to Union Square: 30 mins (starting point)
    # After Jeffrey (Union Square) to Alamo Square: 15 mins
    # After Brian (Alamo Square) to North Beach: 15 mins

    # Constraints for travel:
    # Start at Sunset at 0 mins (9:00AM), travel to Union Square takes 30 mins
    s.add(jeffrey_start >= 30)

    # After Jeffrey, travel to Alamo Square takes 15 mins
    s.add(brian_start >= jeffrey_end + 15)

    # After Brian, travel to North Beach takes 15 mins
    s.add(sarah_start >= brian_end + 15)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def to_time(minutes):
            hours = (minutes // 60) + 9
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        jeffrey_s = m.eval(jeffrey_start).as_long()
        jeffrey_e = m.eval(jeffrey_end).as_long()
        brian_s = m.eval(brian_start).as_long()
        brian_e = m.eval(brian_end).as_long()
        sarah_s = m.eval(sarah_start).as_long()
        sarah_e = m.eval(sarah_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Jeffrey", "start_time": to_time(jeffrey_s), "end_time": to_time(jeffrey_e)},
            {"action": "meet", "person": "Brian", "start_time": to_time(brian_s), "end_time": to_time(brian_e)},
            {"action": "meet", "person": "Sarah", "start_time": to_time(sarah_s), "end_time": to_time(sarah_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Print the solution
import json
print(json.dumps(solve_scheduling(), indent=2))
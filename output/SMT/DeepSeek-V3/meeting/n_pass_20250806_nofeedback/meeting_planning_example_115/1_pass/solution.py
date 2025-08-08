from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Carol's meeting at Marina District
    carol_start = Int('carol_start')  # in minutes from 9:00 AM
    carol_end = Int('carol_end')

    # Jessica's meeting at Pacific Heights
    jessica_start = Int('jessica_start')  # in minutes from 9:00 AM
    jessica_end = Int('jessica_end')

    # Convert time constraints to minutes from 9:00 AM
    # Carol's availability: 11:30 AM (150 mins) to 3:00 PM (360 mins)
    carol_available_start = 150  # 11:30 AM is 2.5 hours after 9:00 AM
    carol_available_end = 360     # 3:00 PM is 6 hours after 9:00 AM

    # Jessica's availability: 3:30 PM (390 mins) to 4:45 PM (465 mins)
    jessica_available_start = 390  # 3:30 PM is 6.5 hours after 9:00 AM
    jessica_available_end = 465    # 4:45 PM is 7.75 hours after 9:00 AM

    # Meeting duration constraints
    s.add(carol_end - carol_start >= 60)  # Carol: 60 minutes
    s.add(jessica_end - jessica_start >= 45)  # Jessica: 45 minutes

    # Meeting must be within their availability windows
    s.add(carol_start >= carol_available_start)
    s.add(carol_end <= carol_available_end)
    s.add(jessica_start >= jessica_available_start)
    s.add(jessica_end <= jessica_available_end)

    # Travel times (in minutes)
    # From Richmond to Marina: 9 minutes (initial location is Richmond at 9:00 AM)
    # From Marina to Pacific Heights: 7 minutes
    # From Pacific Heights to Richmond: 12 minutes (not needed here)

    # Initial travel to Marina to meet Carol
    # Must arrive at Marina by carol_start, starting from Richmond at 9:00 AM (0 mins)
    s.add(carol_start >= 9)  # travel time from Richmond to Marina is 9 minutes

    # Travel from Marina to Pacific Heights after meeting Carol
    # Must arrive at Pacific Heights by jessica_start
    # Time after Carol's meeting ends: carol_end + travel time (7) <= jessica_start
    s.add(jessica_start >= carol_end + 7)

    # Check if the solver can find a feasible solution
    if s.check() == sat:
        m = s.model()
        # Extract values
        carol_s = m.eval(carol_start).as_long()
        carol_e = m.eval(carol_end).as_long()
        jessica_s = m.eval(jessica_start).as_long()
        jessica_e = m.eval(jessica_end).as_long()

        # Convert minutes back to HH:MM format from 9:00 AM base
        def to_time_str(minutes):
            time = datetime.datetime(2023, 1, 1, 9, 0) + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": to_time_str(carol_s), "end_time": to_time_str(carol_e)},
            {"action": "meet", "person": "Jessica", "start_time": to_time_str(jessica_s), "end_time": to_time_str(jessica_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute and print the solution
solution = solve_scheduling()
print(solution)
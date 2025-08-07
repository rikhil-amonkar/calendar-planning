from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Richard at Union Square
    richard_start = Int('richard_start')  # in minutes since 9:00 AM
    richard_end = Int('richard_end')

    # Meeting with Charles at Presidio
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Convert friend availability to minutes since 9:00 AM
    # Richard is available from 8:45 AM to 1:00 PM (which is -15 to 240 minutes from 9:00 AM)
    richard_available_start = -15  # 8:45 AM is 15 minutes before 9:00 AM
    richard_available_end = 240    # 1:00 PM is 4 hours (240 minutes) after 9:00 AM

    # Charles is available from 9:45 AM to 1:00 PM (45 to 240 minutes from 9:00 AM)
    charles_available_start = 45
    charles_available_end = 240

    # Travel times in minutes
    bayview_to_union_square = 17
    bayview_to_presidio = 31
    union_square_to_presidio = 24
    presidio_to_union_square = 22

    # Constraints for Richard's meeting
    s.add(richard_start >= richard_available_start)
    s.add(richard_end <= richard_available_end)
    s.add(richard_end - richard_start >= 120)  # at least 120 minutes

    # Constraints for Charles' meeting
    s.add(charles_start >= charles_available_start)
    s.add(charles_end <= charles_available_end)
    s.add(charles_end - charles_start >= 120)  # at least 120 minutes

    # Initial location: Bayview at 0 minutes (9:00 AM)
    # Possible sequences:
    # Option 1: Bayview -> Union Square (Richard) -> Presidio (Charles)
    # Option 2: Bayview -> Presidio (Charles) -> Union Square (Richard)
    # We'll model both options and let the solver choose the feasible one.

    # Option 1: Meet Richard first, then Charles
    option1 = And(
        richard_start >= bayview_to_union_square,  # travel to Union Square takes 17 minutes
        charles_start >= richard_end + union_square_to_presidio,  # travel from Union Square to Presidio takes 24 minutes
        charles_start <= charles_available_end - 120  # ensure Charles meeting fits within his availability
    )

    # Option 2: Meet Charles first, then Richard
    option2 = And(
        charles_start >= bayview_to_presidio,  # travel to Presidio takes 31 minutes
        richard_start >= charles_end + presidio_to_union_square,  # travel from Presidio to Union Square takes 22 minutes
        richard_start <= richard_available_end - 120  # ensure Richard meeting fits within his availability
    )

    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Get the meeting times
        rs = m.evaluate(richard_start).as_long()
        re = m.evaluate(richard_end).as_long()
        cs = m.evaluate(charles_start).as_long()
        ce = m.evaluate(charles_end).as_long()

        # Convert minutes since 9:00 AM to HH:MM format
        def to_time_str(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        richard_start_time = to_time_str(rs)
        richard_end_time = to_time_str(re)
        charles_start_time = to_time_str(cs)
        charles_end_time = to_time_str(ce)

        # Determine the order of meetings
        if rs < cs:
            itinerary = [
                {"action": "meet", "person": "Richard", "start_time": richard_start_time, "end_time": richard_end_time},
                {"action": "meet", "person": "Charles", "start_time": charles_start_time, "end_time": charles_end_time}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Charles", "start_time": charles_start_time, "end_time": charles_end_time},
                {"action": "meet", "person": "Richard", "start_time": richard_start_time, "end_time": richard_end_time}
            ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(result)
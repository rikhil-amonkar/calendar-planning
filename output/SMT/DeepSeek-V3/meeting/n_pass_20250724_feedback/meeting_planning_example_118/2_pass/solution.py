from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()

    # Define variables for meeting start and end times (in minutes from 9:00 AM)
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Convert availability times to minutes from 9:00 AM (540 minutes since midnight)
    # Richard is available from 8:45 AM to 1:00 PM (8:45 is 525 minutes, 1:00 PM is 780 minutes)
    richard_available_start = 525 - 540  # -15 minutes from 9:00 AM
    richard_available_end = 780 - 540    # 240 minutes from 9:00 AM

    # Charles is available from 9:45 AM to 1:00 PM (9:45 is 585 minutes, 1:00 PM is 780 minutes)
    charles_available_start = 585 - 540  # 45 minutes from 9:00 AM
    charles_available_end = 780 - 540    # 240 minutes from 9:00 AM

    # Add constraints for Richard's meeting
    solver.add(richard_start >= richard_available_start)
    solver.add(richard_end <= richard_available_end)
    solver.add(richard_end - richard_start >= 120)  # at least 120 minutes

    # Add constraints for Charles's meeting
    solver.add(charles_start >= charles_available_start)
    solver.add(charles_end <= charles_available_end)
    solver.add(charles_end - charles_start >= 120)  # at least 120 minutes

    # Travel times (in minutes)
    bayview_to_union_square = 17
    union_square_to_presidio = 24
    bayview_to_presidio = 31
    presidio_to_union_square = 22

    # We start at Bayview at 0 minutes (9:00 AM)
    # Option 1: Bayview -> Union Square (meet Richard) -> Presidio (meet Charles)
    option1_richard_start = bayview_to_union_square
    option1_charles_start = richard_end + union_square_to_presidio
    option1 = And(
        richard_start == option1_richard_start,
        charles_start == option1_charles_start,
        charles_start >= charles_available_start,
        charles_end <= charles_available_end
    )

    # Option 2: Bayview -> Presidio (meet Charles) -> Union Square (meet Richard)
    option2_charles_start = bayview_to_presidio
    option2_richard_start = charles_end + presidio_to_union_square
    option2 = And(
        charles_start == option2_charles_start,
        richard_start == option2_richard_start,
        richard_start >= richard_available_start,
        richard_end <= richard_available_end
    )

    # We need at least one of the options to be true
    solver.add(Or(option1, option2))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        
        # Get the values from the model
        rs = model.evaluate(richard_start).as_long()
        re = model.evaluate(richard_end).as_long()
        cs = model.evaluate(charles_start).as_long()
        ce = model.evaluate(charles_end).as_long()

        # Convert minutes from 9:00 AM back to HH:MM
        base_time = datetime.datetime(2000, 1, 1, 9, 0)  # 9:00 AM base

        def minutes_to_time(minutes):
            time = base_time + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        richard_start_time = minutes_to_time(rs)
        richard_end_time = minutes_to_time(re)
        charles_start_time = minutes_to_time(cs)
        charles_end_time = minutes_to_time(ce)

        # Determine the order of meetings based on which option was satisfied
        if model.evaluate(option1):
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

# Solve the problem and print the result
solution = solve_scheduling_problem()
print(solution)
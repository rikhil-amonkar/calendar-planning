from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting times
    # Laura's meeting start and end times (Mission District)
    laura_start = Int('laura_start')
    laura_end = Int('laura_end')

    # Anthony's meeting start and end times (Financial District)
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    castro_arrival = 540  # 9:00 AM in minutes

    # Laura's availability: 12:15 PM (735) to 7:45 PM (1185)
    laura_available_start = 735
    laura_available_end = 1185

    # Anthony's availability: 12:30 PM (750) to 2:45 PM (885)
    anthony_available_start = 750
    anthony_available_end = 885

    # Meeting duration constraints
    laura_min_duration = 75
    anthony_min_duration = 30

    # Travel times in minutes
    castro_to_mission = 7
    castro_to_financial = 20
    mission_to_financial = 17
    financial_to_mission = 17
    financial_to_castro = 23
    mission_to_castro = 7

    # Constraints for Laura's meeting
    s.add(laura_start >= laura_available_start)
    s.add(laura_end <= laura_available_end)
    s.add(laura_end - laura_start >= laura_min_duration)

    # Constraints for Anthony's meeting
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end - anthony_start >= anthony_min_duration)

    # Possible schedules:
    # Option 1: Meet Anthony first, then Laura
    # Option 2: Meet Laura first, then Anthony

    # We'll model both options and let Z3 choose the feasible one.

    # Option 1: Anthony first, then Laura
    option1 = And(
        # Travel from Castro to Financial to meet Anthony
        anthony_start >= castro_arrival + castro_to_financial,
        # Travel from Financial to Mission to meet Laura
        laura_start >= anthony_end + financial_to_mission
    )

    # Option 2: Laura first, then Anthony
    option2 = And(
        # Travel from Castro to Mission to meet Laura
        laura_start >= castro_arrival + castro_to_mission,
        # Travel from Mission to Financial to meet Anthony
        anthony_start >= laura_end + mission_to_financial,
        # Check if Anthony's meeting can fit after Laura
        anthony_start <= anthony_available_end - anthony_min_duration
    )

    # Add either option1 or option2 to the solver
    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Get the meeting times
        laura_s = m.evaluate(laura_start).as_long()
        laura_e = m.evaluate(laura_end).as_long()
        anthony_s = m.evaluate(anthony_start).as_long()
        anthony_e = m.evaluate(anthony_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = []
        # Determine the order of meetings based on start times
        if anthony_s < laura_s:
            # Anthony first
            itinerary.append({
                "action": "meet",
                "person": "Anthony",
                "start_time": minutes_to_time(anthony_s),
                "end_time": minutes_to_time(anthony_e)
            })
            itinerary.append({
                "action": "meet",
                "person": "Laura",
                "start_time": minutes_to_time(laura_s),
                "end_time": minutes_to_time(laura_e)
            })
        else:
            # Laura first
            itinerary.append({
                "action": "meet",
                "person": "Laura",
                "start_time": minutes_to_time(laura_s),
                "end_time": minutes_to_time(laura_e)
            })
            itinerary.append({
                "action": "meet",
                "person": "Anthony",
                "start_time": minutes_to_time(anthony_s),
                "end_time": minutes_to_time(anthony_e)
            })

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Execute and print the solution
solution = solve_scheduling()
print(solution)
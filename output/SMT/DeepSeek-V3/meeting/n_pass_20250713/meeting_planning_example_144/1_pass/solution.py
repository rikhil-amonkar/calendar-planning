from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Laura in Mission District
    laura_start = Int('laura_start')
    laura_end = Int('laura_end')
    # Meeting with Anthony in Financial District
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')

    # Define travel times (in minutes)
    castro_to_mission = 7
    castro_to_financial = 20
    mission_to_financial = 17
    financial_to_mission = 17

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Laura's availability: 12:15 PM (735 minutes) to 7:45 PM (1170 minutes)
    laura_min_start = 735
    laura_max_end = 1170
    # Anthony's availability: 12:30 PM (750 minutes) to 2:45 PM (885 minutes)
    anthony_min_start = 750
    anthony_max_end = 885

    # Constraints for Laura's meeting
    s.add(laura_start >= laura_min_start)
    s.add(laura_end <= laura_max_end)
    s.add(laura_end - laura_start >= 75)  # at least 75 minutes

    # Constraints for Anthony's meeting
    s.add(anthony_start >= anthony_min_start)
    s.add(anthony_end <= anthony_max_end)
    s.add(anthony_end - anthony_start >= 30)  # at least 30 minutes

    # Initial location: The Castro at 9:00 AM (540 minutes)
    # We need to decide the order of meetings: Laura first or Anthony first

    # Option 1: Meet Laura first, then Anthony
    option1 = And(
        laura_start >= 540 + castro_to_mission,  # travel from Castro to Mission
        anthony_start >= laura_end + mission_to_financial  # travel from Mission to Financial
    )

    # Option 2: Meet Anthony first, then Laura
    option2 = And(
        anthony_start >= 540 + castro_to_financial,  # travel from Castro to Financial
        laura_start >= anthony_end + financial_to_mission  # travel from Financial to Mission
    )

    # Add constraints that either option1 or option2 must be true
    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        laura_start_val = m.evaluate(laura_start).as_long()
        laura_end_val = m.evaluate(laura_end).as_long()
        anthony_start_val = m.evaluate(anthony_start).as_long()
        anthony_end_val = m.evaluate(anthony_end).as_long()

        # Determine the order
        if laura_start_val + castro_to_mission <= anthony_start_val - mission_to_financial:
            order = "Meet Laura first, then Anthony"
        else:
            order = "Meet Anthony first, then Laura"

        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            hours = (minutes // 60) % 24
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        print("SOLUTION:")
        print(f"Order: {order}")
        print(f"Meet Laura from {minutes_to_time(laura_start_val)} to {minutes_to_time(laura_end_val)}")
        print(f"Meet Anthony from {minutes_to_time(anthony_start_val)} to {minutes_to_time(anthony_end_val)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()
from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert times to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define variables for meeting start and end times
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Define variables for travel times
    travel1_start = Int('travel1_start')
    travel1_end = Int('travel1_end')
    travel2_start = Int('travel2_start')
    travel2_end = Int('travel2_end')

    # Starting at Financial District at 9:00 AM (540 minutes)
    current_time = time_to_minutes("09:00")

    # Barbara's availability: 8:15 AM to 7:00 PM (495 to 1140 minutes)
    barbara_available_start = time_to_minutes("08:15")
    barbara_available_end = time_to_minutes("19:00")
    # Kenneth's availability: 12:00 PM to 3:00 PM (720 to 900 minutes)
    kenneth_available_start = time_to_minutes("12:00")
    kenneth_available_end = time_to_minutes("15:00")

    # Meeting durations
    barbara_duration = 45
    kenneth_duration = 90

    # Travel times in minutes
    fd_to_china = 5
    fd_to_ggp = 23
    china_to_ggp = 23
    ggp_to_china = 23
    ggp_to_fd = 26
    china_to_fd = 5

    # Scenario 1: Meet Barbara first, then Kenneth
    # Travel from Financial District to Golden Gate Park: 23 minutes
    travel1_start_sc1 = current_time
    travel1_end_sc1 = travel1_start_sc1 + fd_to_ggp
    # Meet Barbara
    barbara_start_sc1 = travel1_end_sc1
    barbara_end_sc1 = barbara_start_sc1 + barbara_duration
    # Travel from Golden Gate Park to Chinatown: 23 minutes
    travel2_start_sc1 = barbara_end_sc1
    travel2_end_sc1 = travel2_start_sc1 + ggp_to_china
    # Meet Kenneth
    kenneth_start_sc1 = travel2_end_sc1
    kenneth_end_sc1 = kenneth_start_sc1 + kenneth_duration

    # Scenario 2: Meet Kenneth first, then Barbara
    # Travel from Financial District to Chinatown: 5 minutes
    travel1_start_sc2 = current_time
    travel1_end_sc2 = travel1_start_sc2 + fd_to_china
    # Meet Kenneth
    kenneth_start_sc2 = travel1_end_sc2
    kenneth_end_sc2 = kenneth_start_sc2 + kenneth_duration
    # Travel from Chinatown to Golden Gate Park: 23 minutes
    travel2_start_sc2 = kenneth_end_sc2
    travel2_end_sc2 = travel2_start_sc2 + china_to_ggp
    # Meet Barbara
    barbara_start_sc2 = travel2_end_sc2
    barbara_end_sc2 = barbara_start_sc2 + barbara_duration

    # Check if Scenario 1 is feasible
    scenario1 = And(
        barbara_start_sc1 >= barbara_available_start,
        barbara_end_sc1 <= barbara_available_end,
        kenneth_start_sc1 >= kenneth_available_start,
        kenneth_end_sc1 <= kenneth_available_end
    )

    # Check if Scenario 2 is feasible
    scenario2 = And(
        kenneth_start_sc2 >= kenneth_available_start,
        kenneth_end_sc2 <= kenneth_available_end,
        barbara_start_sc2 >= barbara_available_start,
        barbara_end_sc2 <= barbara_available_end
    )

    # Add either scenario to the solver
    s.add(Or(scenario1, scenario2))

    # Check for feasibility
    if s.check() == sat:
        m = s.model()
        # Determine which scenario was chosen
        if is_true(m.eval(scenario1)):
            # Scenario 1 was chosen
            barbara_start_time = minutes_to_time(barbara_start_sc1)
            barbara_end_time = minutes_to_time(barbara_end_sc1)
            kenneth_start_time = minutes_to_time(kenneth_start_sc1)
            kenneth_end_time = minutes_to_time(kenneth_end_sc1)
            itinerary = [
                {"action": "meet", "person": "Barbara", "start_time": barbara_start_time, "end_time": barbara_end_time},
                {"action": "meet", "person": "Kenneth", "start_time": kenneth_start_time, "end_time": kenneth_end_time}
            ]
        else:
            # Scenario 2 was chosen
            kenneth_start_time = minutes_to_time(kenneth_start_sc2)
            kenneth_end_time = minutes_to_time(kenneth_end_sc2)
            barbara_start_time = minutes_to_time(barbara_start_sc2)
            barbara_end_time = minutes_to_time(barbara_end_sc2)
            itinerary = [
                {"action": "meet", "person": "Kenneth", "start_time": kenneth_start_time, "end_time": kenneth_end_time},
                {"action": "meet", "person": "Barbara", "start_time": barbara_start_time, "end_time": barbara_end_time}
            ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(result)
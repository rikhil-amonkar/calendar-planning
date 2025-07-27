from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    meet_jason_start = Int('meet_jason_start')
    meet_jason_end = Int('meet_jason_end')
    meet_kenneth_start = Int('meet_kenneth_start')
    meet_kenneth_end = Int('meet_kenneth_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    jason_available_start = 60  # 10:00 AM is 60 minutes after 9:00 AM
    jason_available_end = 435    # 4:15 PM is 435 minutes after 9:00 AM
    kenneth_available_start = 390  # 3:30 PM is 390 minutes after 9:00 AM
    kenneth_available_end = 465    # 4:45 PM is 465 minutes after 9:00 AM

    # Travel times in minutes
    ph_to_presidio = 11
    ph_to_marina = 6
    presidio_to_marina = 10
    marina_to_presidio = 10

    # Constraints for Jason's meeting
    s.add(meet_jason_start >= jason_available_start)
    s.add(meet_jason_end <= jason_available_end)
    s.add(meet_jason_end - meet_jason_start >= 90)  # at least 90 minutes

    # Constraints for Kenneth's meeting
    s.add(meet_kenneth_start >= kenneth_available_start)
    s.add(meet_kenneth_end <= kenneth_available_end)
    s.add(meet_kenneth_end - meet_kenneth_start >= 45)  # at least 45 minutes

    # Scenario 1: Meet Jason first, then Kenneth
    # Travel from Pacific Heights to Presidio: 11 minutes
    # Then from Presidio to Marina District: 10 minutes
    scenario1 = And(
        meet_jason_start >= 11,  # travel from PH to Presidio
        meet_kenneth_start >= meet_jason_end + 10  # travel from Presidio to Marina
    )

    # Scenario 2: Meet Kenneth first, then Jason
    # Travel from Pacific Heights to Marina: 6 minutes
    # Then from Marina to Presidio: 10 minutes
    scenario2 = And(
        meet_kenneth_start >= 6,  # travel from PH to Marina
        meet_jason_start >= meet_kenneth_end + 10  # travel from Marina to Presidio
    )

    # Ensure at least one scenario is satisfied
    s.add(Or(scenario1, scenario2))

    # Check for feasibility
    if s.check() == sat:
        m = s.model()
        jason_start = m.eval(meet_jason_start).as_long()
        jason_end = m.eval(meet_jason_end).as_long()
        kenneth_start = m.eval(meet_kenneth_start).as_long()
        kenneth_end = m.eval(meet_kenneth_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Jason", "start_time": minutes_to_time(jason_start), "end_time": minutes_to_time(jason_end)},
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start), "end_time": minutes_to_time(kenneth_end)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute and print the solution
solution = solve_scheduling_problem()
print(solution)
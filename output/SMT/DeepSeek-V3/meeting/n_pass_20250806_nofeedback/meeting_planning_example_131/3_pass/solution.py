from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight for easier arithmetic
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Constants
    start_time = time_to_minutes("09:00")  # 9:00 AM in minutes
    jason_start = time_to_minutes("10:00")
    jason_end = time_to_minutes("16:15")  # 4:15 PM
    kenneth_start = time_to_minutes("15:30")  # 3:30 PM
    kenneth_end = time_to_minutes("16:45")   # 4:45 PM

    # Travel times in minutes
    travel_PH_to_Presidio = 11
    travel_PH_to_Marina = 6
    travel_Presidio_to_Marina = 10
    travel_Marina_to_Presidio = 10
    travel_Presidio_to_PH = 11
    travel_Marina_to_PH = 7

    # Variables for meeting times
    jason_meet_start = Int('jason_meet_start')
    jason_meet_end = Int('jason_meet_end')
    kenneth_meet_start = Int('kenneth_meet_start')
    kenneth_meet_end = Int('kenneth_meet_end')

    # Constraints for Jason
    s.add(jason_meet_start >= jason_start)
    s.add(jason_meet_end <= jason_end)
    s.add(jason_meet_end - jason_meet_start >= 90)  # at least 90 minutes

    # Constraints for Kenneth
    s.add(kenneth_meet_start >= kenneth_start)
    s.add(kenneth_meet_end <= kenneth_end)
    s.add(kenneth_meet_end - kenneth_meet_start >= 45)  # at least 45 minutes

    # Option 1: Meet Jason first, then Kenneth
    # Travel from Pacific Heights to Presidio to meet Jason: 11 minutes
    option1_jason_start = start_time + travel_PH_to_Presidio
    option1_jason_end = option1_jason_start + 90  # Minimum meeting duration
    # Then travel from Presidio to Marina to meet Kenneth: 10 minutes
    option1_kenneth_start = option1_jason_end + travel_Presidio_to_Marina
    option1_kenneth_end = option1_kenneth_start + 45  # Minimum meeting duration

    # Constraints for Option 1
    s.push()
    s.add(jason_meet_start == option1_jason_start)
    s.add(jason_meet_end == option1_jason_end)
    s.add(kenneth_meet_start == option1_kenneth_start)
    s.add(kenneth_meet_end == option1_kenneth_end)
    s.add(option1_kenneth_end <= kenneth_end)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        j_start = model.eval(jason_meet_start).as_long()
        j_end = model.eval(jason_meet_end).as_long()
        k_start = model.eval(kenneth_meet_start).as_long()
        k_end = model.eval(kenneth_meet_end).as_long()

        itinerary.append({
            "action": "meet",
            "person": "Jason",
            "start_time": minutes_to_time(j_start),
            "end_time": minutes_to_time(j_end)
        })
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_time(k_start),
            "end_time": minutes_to_time(k_end)
        })
        s.pop()
        return {"itinerary": itinerary}

    s.pop()

    # Option 2: Meet Kenneth first, then Jason
    # Travel from Pacific Heights to Marina to meet Kenneth: 6 minutes
    option2_kenneth_start = start_time + travel_PH_to_Marina
    option2_kenneth_end = option2_kenneth_start + 45  # Minimum meeting duration
    # Then travel from Marina to Presidio to meet Jason: 10 minutes
    option2_jason_start = option2_kenneth_end + travel_Marina_to_Presidio
    option2_jason_end = option2_jason_start + 90  # Minimum meeting duration

    # Constraints for Option 2
    s.push()
    s.add(kenneth_meet_start == option2_kenneth_start)
    s.add(kenneth_meet_end == option2_kenneth_end)
    s.add(jason_meet_start == option2_jason_start)
    s.add(jason_meet_end == option2_jason_end)
    s.add(option2_jason_end <= jason_end)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        j_start = model.eval(jason_meet_start).as_long()
        j_end = model.eval(jason_meet_end).as_long()
        k_start = model.eval(kenneth_meet_start).as_long()
        k_end = model.eval(kenneth_meet_end).as_long()

        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_time(k_start),
            "end_time": minutes_to_time(k_end)
        })
        itinerary.append({
            "action": "meet",
            "person": "Jason",
            "start_time": minutes_to_time(j_start),
            "end_time": minutes_to_time(j_end)
        })
        s.pop()
        return {"itinerary": itinerary}

    s.pop()

    # If no feasible schedule found
    return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(result)
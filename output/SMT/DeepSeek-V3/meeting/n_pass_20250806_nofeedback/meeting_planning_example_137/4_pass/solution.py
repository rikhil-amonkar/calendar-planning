from z3 import *

def solve_scheduling():
    s = Solver()

    # Convert time strings to minutes since midnight
    def time_to_min(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    def min_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Meeting durations in minutes
    barbara_duration = 45
    kenneth_duration = 90

    # Travel times in minutes
    fd_to_china = 5
    fd_to_ggp = 23
    china_to_ggp = 23
    ggp_to_china = 23

    # Availability windows in minutes
    barbara_start_avail = time_to_min("08:15")
    barbara_end_avail = time_to_min("19:00")
    kenneth_start_avail = time_to_min("12:00")
    kenneth_end_avail = time_to_min("15:00")

    # Starting time at Financial District
    start_time = time_to_min("09:00")

    # Decision variables
    meet_barbara = Bool('meet_barbara')
    meet_kenneth = Bool('meet_kenneth')

    # Meeting times
    barbara_start = Int('barbara_start')
    barbara_end = barbara_start + barbara_duration
    kenneth_start = Int('kenneth_start')
    kenneth_end = kenneth_start + kenneth_duration

    # Travel sequences
    # Option 1: FD -> GGP -> China
    travel1_start = start_time
    travel1_end = travel1_start + fd_to_ggp
    barbara_start1 = travel1_end
    barbara_end1 = barbara_start1 + barbara_duration
    travel2_start1 = barbara_end1
    travel2_end1 = travel2_start1 + ggp_to_china
    kenneth_start1 = travel2_end1
    kenneth_end1 = kenneth_start1 + kenneth_duration

    # Option 2: FD -> China -> GGP
    travel1_start2 = start_time
    travel1_end2 = travel1_start2 + fd_to_china
    kenneth_start2 = travel1_end2
    kenneth_end2 = kenneth_start2 + kenneth_duration
    travel2_start2 = kenneth_end2
    travel2_end2 = travel2_start2 + china_to_ggp
    barbara_start2 = travel2_end2
    barbara_end2 = barbara_start2 + barbara_duration

    # Constraints for Option 1
    option1 = And(
        meet_barbara,
        meet_kenneth,
        barbara_start1 >= barbara_start_avail,
        barbara_end1 <= barbara_end_avail,
        kenneth_start1 >= kenneth_start_avail,
        kenneth_end1 <= kenneth_end_avail
    )

    # Constraints for Option 2
    option2 = And(
        meet_barbara,
        meet_kenneth,
        kenneth_start2 >= kenneth_start_avail,
        kenneth_end2 <= kenneth_end_avail,
        barbara_start2 >= barbara_start_avail,
        barbara_end2 <= barbara_end_avail
    )

    # Add constraints
    s.add(Or(option1, option2))

    if s.check() == sat:
        m = s.model()
        if is_true(m.eval(option1)):
            itinerary = [
                {"action": "meet", "person": "Barbara", 
                 "start_time": min_to_time(barbara_start1),
                 "end_time": min_to_time(barbara_end1)},
                {"action": "meet", "person": "Kenneth",
                 "start_time": min_to_time(kenneth_start1),
                 "end_time": min_to_time(kenneth_end1)}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Kenneth",
                 "start_time": min_to_time(kenneth_start2),
                 "end_time": min_to_time(kenneth_end2)},
                {"action": "meet", "person": "Barbara",
                 "start_time": min_to_time(barbara_start2),
                 "end_time": min_to_time(barbara_end2)}
            ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(result)
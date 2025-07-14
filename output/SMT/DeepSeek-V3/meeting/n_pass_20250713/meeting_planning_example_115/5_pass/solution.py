from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    arrival_time = 540  # 9:00 AM

    # Friends' availability windows
    carol_start_min = 690  # 11:30 AM
    carol_end_max = 900    # 3:00 PM
    jessica_start_min = 1050  # 3:30 PM
    jessica_end_max = 1125    # 4:45 PM

    # Meeting durations
    carol_duration = 60
    jessica_duration = 45

    # Travel times (minutes)
    travel_to_marina = 9    # Richmond → Marina
    travel_marina_to_pacific = 7  # Marina → Pacific Heights
    travel_pacific_to_richmond = 12  # Pacific Heights → Richmond

    # Meeting time variables
    meet_carol_start = Int('meet_carol_start')
    meet_carol_end = Int('meet_carol_end')
    meet_jessica_start = Int('meet_jessica_start')
    meet_jessica_end = Int('meet_jessica_end')

    # Carol's meeting constraints
    s.add(meet_carol_start >= carol_start_min)
    s.add(meet_carol_end <= carol_end_max)
    s.add(meet_carol_end == meet_carol_start + carol_duration)

    # Jessica's meeting constraints
    s.add(meet_jessica_start >= jessica_start_min)
    s.add(meet_jessica_end <= jessica_end_max)
    s.add(meet_jessica_end == meet_jessica_start + jessica_duration)

    # Travel constraints
    s.add(meet_carol_start >= arrival_time + travel_to_marina)
    s.add(meet_jessica_start >= meet_carol_end + travel_marina_to_pacific)

    # Check feasibility
    if s.check() == sat:
        m = s.model()
        carol_start = m.evaluate(meet_carol_start).as_long()
        carol_end = m.evaluate(meet_carol_end).as_long()
        jessica_start = m.evaluate(meet_jessica_start).as_long()
        jessica_end = m.evaluate(meet_jessica_end).as_long()

        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d} {'AM' if h < 12 else 'PM'}"

        print("SOLUTION:")
        print(f"Meet Carol from {minutes_to_time(carol_start)} to {minutes_to_time(carol_end)} in Marina District")
        print(f"Meet Jessica from {minutes_to_time(jessica_start)} to {minutes_to_time(jessica_end)} in Pacific Heights")
    else:
        print("No feasible schedule exists that meets all constraints")

solve_scheduling()
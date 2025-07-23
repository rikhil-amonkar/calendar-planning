from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Arrival time at Richmond District: 9:00 AM (540 minutes)
    arrival_time = 540

    # Carol's availability: 11:30 AM (690) to 3:00 PM (900)
    carol_start_min = 690
    carol_end_max = 900
    # Jessica's availability: 3:30 PM (1050) to 4:45 PM (1125)
    jessica_start_min = 1050
    jessica_end_max = 1125

    # Meeting durations in minutes
    carol_duration = 60
    jessica_duration = 45

    # Travel times in minutes
    # From Richmond to Pacific Heights: 10
    # From Richmond to Marina: 9
    # From Pacific Heights to Marina: 6
    # From Marina to Pacific Heights: 7
    # From Pacific Heights to Richmond: 12
    # From Marina to Richmond: 11

    # Variables for meeting start times
    meet_carol_start = Int('meet_carol_start')
    meet_carol_end = Int('meet_carol_end')
    meet_jessica_start = Int('meet_jessica_start')
    meet_jessica_end = Int('meet_jessica_end')

    # Constraints for Carol's meeting
    s.add(meet_carol_start >= carol_start_min)
    s.add(meet_carol_end <= carol_end_max)
    s.add(meet_carol_end == meet_carol_start + carol_duration)

    # Constraints for Jessica's meeting
    s.add(meet_jessica_start >= jessica_start_min)
    s.add(meet_jessica_end <= jessica_end_max)
    s.add(meet_jessica_end == meet_jessica_start + jessica_duration)

    # Determine the order of meetings and travel times
    # We have two options: meet Carol first or Jessica first. But Jessica's window is later, so Carol must be first.

    # Option 1: Richmond -> Marina (Carol) -> Pacific Heights (Jessica) -> Richmond
    travel_to_carol = 9  # Richmond to Marina
    travel_carol_to_jessica = 7  # Marina to Pacific Heights
    travel_jessica_to_richmond = 12  # Pacific Heights to Richmond

    # Start by going to Marina to meet Carol
    s.add(meet_carol_start >= arrival_time + travel_to_carol)
    # After meeting Carol, go to Pacific Heights to meet Jessica
    s.add(meet_jessica_start >= meet_carol_end + travel_carol_to_jessica)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        carol_start = m.evaluate(meet_carol_start).as_long()
        carol_end = m.evaluate(meet_carol_end).as_long()
        jessica_start = m.evaluate(meet_jessica_start).as_long()
        jessica_end = m.evaluate(meet_jessica_end).as_long()

        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            h = (minutes // 60) % 24
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        carol_start_time = minutes_to_time(carol_start)
        carol_end_time = minutes_to_time(carol_end)
        jessica_start_time = minutes_to_time(jessica_start)
        jessica_end_time = minutes_to_time(jessica_end)

        # Ensure Jessica's meeting is within her availability
        if jessica_start >= jessica_start_min and jessica_end <= jessica_end_max:
            print("SOLUTION:")
            print(f"Meet Carol from {carol_start_time} to {carol_end_time} in Marina District.")
            print(f"Meet Jessica from {jessica_start_time} to {jessica_end_time} in Pacific Heights.")
        else:
            print("No feasible schedule found that meets all constraints.")
    else:
        print("No feasible schedule found.")

solve_scheduling()
from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Carol's availability: 11:30 AM (690) to 3:00 PM (900)
    carol_start_avail = 690  # 11:30 AM in minutes since midnight
    carol_end_avail = 900    # 3:00 PM in minutes since midnight

    # Jessica's availability: 3:30 PM (1050) to 4:45 PM (1125)
    jessica_start_avail = 1050  # 3:30 PM
    jessica_end_avail = 1125    # 4:45 PM

    # Variables for meeting start and end times
    meet_carol_start = Int('meet_carol_start')
    meet_carol_end = Int('meet_carol_end')
    meet_jessica_start = Int('meet_jessica_start')
    meet_jessica_end = Int('meet_jessica_end')

    # Travel times (in minutes)
    # From Richmond to Marina: 9
    # From Marina to Pacific Heights: 7
    # From Richmond to Pacific Heights: 10
    # From Pacific Heights to Marina: 6
    # From Marina to Richmond: 11
    # From Pacific Heights to Richmond: 12

    # Constraints for Carol (Marina District)
    s.add(meet_carol_start >= carol_start_avail)
    s.add(meet_carol_end <= carol_end_avail)
    s.add(meet_carol_end - meet_carol_start >= 60)  # at least 60 minutes

    # Constraints for Jessica (Pacific Heights)
    s.add(meet_jessica_start >= jessica_start_avail)
    s.add(meet_jessica_end <= jessica_end_avail)
    s.add(meet_jessica_end - meet_jessica_start >= 45)  # at least 45 minutes

    # Starting at Richmond at 9:00 AM (540)
    # Need to reach Carol (Marina) or Jessica (Pacific Heights) first.
    # Let's model both possibilities: meeting Carol first or Jessica first.

    # Option 1: Meet Carol first, then Jessica
    # Travel from Richmond to Marina: 9 minutes (arrive at Marina at 540 + 9 = 549)
    # So meet_carol_start >= 549
    # Then after meeting Carol, travel to Pacific Heights: 7 minutes
    # So meet_jessica_start >= meet_carol_end + 7
    # But Jessica's availability starts at 1050, so meet_jessica_start >= 1050
    # So meet_carol_end + 7 <= meet_jessica_start
    # And meet_carol_end + 7 <= 1125 - 45 = 1080 (since meet_jessica_end <= 1125)
    # So this path is possible if meet_carol_end <= 1080 -7 = 1073

    # Option 2: Meet Jessica first, then Carol
    # But Carol's availability ends at 900, and Jessica's starts at 1050.
    # Travel from Richmond to Pacific Heights: 10 minutes (arrive at 540 +10 = 550)
    # But Jessica's availability starts at 1050, so waiting from 550 to 1050 is 500 minutes, which is too long.
    # Then after meeting Jessica, travel to Marina: 6 minutes, but Carol's availability ends at 900, which is before Jessica's meeting starts.
    # So this path is impossible.

    # Thus, only Option 1 is feasible.

    # Add constraints for Option 1
    s.add(meet_carol_start >= 540 + 9)  # arrive at Marina at 549
    s.add(meet_jessica_start >= meet_carol_end + 7)  # travel to Pacific Heights after meeting Carol
    s.add(meet_jessica_start >= jessica_start_avail)  # Jessica's availability starts at 1050

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        carol_s = m.eval(meet_carol_start).as_long()
        carol_e = m.eval(meet_carol_end).as_long()
        jessica_s = m.eval(meet_jessica_start).as_long()
        jessica_e = m.eval(meet_jessica_end).as_long()

        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"

        print("SOLUTION:")
        print(f"Meet Carol from {minutes_to_time(carol_s)} to {minutes_to_time(carol_e)}")
        print(f"Meet Jessica from {minutes_to_time(jessica_s)} to {minutes_to_time(jessica_e)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()
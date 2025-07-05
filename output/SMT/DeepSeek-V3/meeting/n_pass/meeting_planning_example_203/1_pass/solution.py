from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Meeting durations in minutes
    david_duration = 15
    timothy_duration = 75
    robert_duration = 90

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    start_of_day = 9 * 60  # 9:00 AM in minutes

    # Friends' availability windows in minutes since start_of_day
    # David: 10:45 AM to 3:30 PM -> 105 to 390 minutes since 9:00 AM
    david_start_min = 105  # 10:45 AM - 9:00 AM = 1h45m = 105m
    david_end_max = 390    # 3:30 PM - 9:00 AM = 6h30m = 390m

    # Timothy: 9:00 AM to 3:30 PM -> 0 to 390 minutes
    timothy_start_min = 0
    timothy_end_max = 390

    # Robert: 12:15 PM to 7:45 PM -> 195 to 645 minutes
    robert_start_min = 195  # 12:15 PM - 9:00 AM = 3h15m = 195m
    robert_end_max = 645     # 7:45 PM - 9:00 AM = 10h45m = 645m

    # Variables for meeting start times (in minutes since 9:00 AM)
    meet_david_start = Int('meet_david_start')
    meet_timothy_start = Int('meet_timothy_start')
    meet_robert_start = Int('meet_robert_start')

    # Variables for meeting end times
    meet_david_end = meet_david_start + david_duration
    meet_timothy_end = meet_timothy_start + timothy_duration
    meet_robert_end = meet_robert_start + robert_duration

    # Variables to track the order of meetings and travel times
    # We need to decide the order in which to meet friends to minimize conflicts

    # Possible orders: e.g., Timothy -> David -> Robert, etc.
    # We'll model the sequence by enforcing constraints on start and end times plus travel

    # Travel times between locations (in minutes)
    travel_FD_to_FW = 10  # Financial District to Fisherman's Wharf
    travel_FD_to_PH = 13  # Financial District to Pacific Heights
    travel_FD_to_MD = 17  # Financial District to Mission District

    travel_FW_to_FD = 11  # Fisherman's Wharf to Financial District
    travel_FW_to_PH = 12  # Fisherman's Wharf to Pacific Heights
    travel_FW_to_MD = 22  # Fisherman's Wharf to Mission District

    travel_PH_to_FD = 13  # Pacific Heights to Financial District
    travel_PH_to_FW = 13  # Pacific Heights to Fisherman's Wharf
    travel_PH_to_MD = 15  # Pacific Heights to Mission District

    travel_MD_to_FD = 17  # Mission District to Financial District
    travel_MD_to_FW = 22  # Mission District to Fisherman's Wharf
    travel_MD_to_PH = 16  # Mission District to Pacific Heights

    # We start at Financial District at time 0 (9:00 AM)

    # Let's assume the order is Timothy (Pacific Heights) -> David (Fisherman's Wharf) -> Robert (Mission District)
    # This is one possible order; other orders may also be possible

    # Constraints for this order:
    # 1. Go to Pacific Heights (Timothy) from Financial District: time 0 to travel_FD_to_PH
    #    meet_timothy_start >= travel_FD_to_PH
    s.add(meet_timothy_start >= travel_FD_to_PH)

    # 2. After meeting Timothy, travel to Fisherman's Wharf (David): time meet_timothy_end + travel_PH_to_FW
    #    meet_david_start >= meet_timothy_end + travel_PH_to_FW
    s.add(meet_david_start >= meet_timothy_end + travel_PH_to_FW)

    # 3. After meeting David, travel to Mission District (Robert): time meet_david_end + travel_FW_to_MD
    #    meet_robert_start >= meet_david_end + travel_FW_to_MD
    s.add(meet_robert_start >= meet_david_end + travel_FW_to_MD)

    # Meeting time windows
    # David must be met between david_start_min and david_end_max - duration
    s.add(meet_david_start >= david_start_min)
    s.add(meet_david_end <= david_end_max)

    # Timothy must be met between timothy_start_min and timothy_end_max - duration
    s.add(meet_timothy_start >= timothy_start_min)
    s.add(meet_timothy_end <= timothy_end_max)

    # Robert must be met between robert_start_min and robert_end_max - duration
    s.add(meet_robert_start >= robert_start_min)
    s.add(meet_robert_end <= robert_end_max)

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        # Convert times back to hours and minutes
        def minutes_to_time(minutes):
            h = (minutes + start_of_day) // 60
            m = (minutes + start_of_day) % 60
            return f"{h}:{m:02d}"

        david_start = m.evaluate(meet_david_start).as_long()
        timothy_start = m.evaluate(meet_timothy_start).as_long()
        robert_start = m.evaluate(meet_robert_start).as_long()

        print("SOLUTION:")
        print(f"Meet Timothy at Pacific Heights from {minutes_to_time(timothy_start)} to {minutes_to_time(timothy_start + timothy_duration)}")
        print(f"Then meet David at Fisherman's Wharf from {minutes_to_time(david_start)} to {minutes_to_time(david_start + david_duration)}")
        print(f"Then meet Robert at Mission District from {minutes_to_time(robert_start)} to {minutes_to_time(robert_start + robert_duration)}")
    else:
        print("No valid schedule found.")

solve_scheduling()
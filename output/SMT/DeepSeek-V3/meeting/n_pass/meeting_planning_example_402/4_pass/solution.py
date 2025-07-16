from z3 import *

def main():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Arrival time at Golden Gate Park: 9:00 AM (540)
    # Define friends' availability windows in minutes since 9:00 AM
    # Sarah: Haight-Ashbury, 5:00 PM (1020) to 9:30 PM (1290), min 105 minutes
    sarah_start = 1020 - 540  # 480 minutes since 9:00 AM
    sarah_end = 1290 - 540    # 750 minutes since 9:00 AM
    sarah_min = 105

    # Patricia: Sunset District, 5:00 PM (1020) to 7:45 PM (1185), min 45 minutes
    patricia_start = 1020 - 540  # 480 minutes since 9:00 AM
    patricia_end = 1185 - 540    # 645 minutes since 9:00 AM
    patricia_min = 45

    # Matthew: Marina District, 9:15 AM (555) to 12:00 PM (720), min 15 minutes
    matthew_start = 555 - 540    # 15 minutes since 9:00 AM
    matthew_end = 720 - 540      # 180 minutes since 9:00 AM
    matthew_min = 15

    # Joseph: Financial District, 2:15 PM (855) to 6:45 PM (1125), min 30 minutes
    joseph_start = 855 - 540     # 315 minutes since 9:00 AM
    joseph_end = 1125 - 540      # 585 minutes since 9:00 AM
    joseph_min = 30

    # Robert: Union Square, 10:15 AM (615) to 9:45 PM (1305), min 15 minutes
    robert_start = 615 - 540     # 75 minutes since 9:00 AM
    robert_end = 1305 - 540      # 765 minutes since 9:00 AM
    robert_min = 15

    # Define variables for each meeting's start and end times
    meet_sarah_start = Int('meet_sarah_start')
    meet_sarah_end = Int('meet_sarah_end')
    meet_patricia_start = Int('meet_patricia_start')
    meet_patricia_end = Int('meet_patricia_end')
    meet_matthew_start = Int('meet_matthew_start')
    meet_matthew_end = Int('meet_matthew_end')
    meet_joseph_start = Int('meet_joseph_start')
    meet_joseph_end = Int('meet_joseph_end')
    meet_robert_start = Int('meet_robert_start')
    meet_robert_end = Int('meet_robert_end')

    # Add constraints for each meeting's duration and availability
    # Sarah
    s.add(meet_sarah_start >= sarah_start)
    s.add(meet_sarah_end <= sarah_end)
    s.add(meet_sarah_end - meet_sarah_start >= sarah_min)
    # Patricia
    s.add(meet_patricia_start >= patricia_start)
    s.add(meet_patricia_end <= patricia_end)
    s.add(meet_patricia_end - meet_patricia_start >= patricia_min)
    # Matthew
    s.add(meet_matthew_start >= matthew_start)
    s.add(meet_matthew_end <= matthew_end)
    s.add(meet_matthew_end - meet_matthew_start >= matthew_min)
    # Joseph
    s.add(meet_joseph_start >= joseph_start)
    s.add(meet_joseph_end <= joseph_end)
    s.add(meet_joseph_end - meet_joseph_start >= joseph_min)
    # Robert
    s.add(meet_robert_start >= robert_start)
    s.add(meet_robert_end <= robert_end)
    s.add(meet_robert_end - meet_robert_start >= robert_min)

    # Define travel times between locations in minutes
    # From Golden Gate Park to Marina: 16
    # From Marina to Union Square: 16
    # From Union Square to Financial: 9
    # From Financial to Sunset: 31
    # From Sunset to Haight: 15

    # Current location starts at Golden Gate Park (time 0)
    s.add(meet_matthew_start >= 0 + 16)  # Travel to Marina takes 16 minutes

    # After Matthew, travel to Union Square: 16 minutes
    s.add(meet_robert_start >= meet_matthew_end + 16)

    # After Robert, travel to Financial: 9 minutes
    s.add(meet_joseph_start >= meet_robert_end + 9)

    # After Joseph, travel to Sunset: 31 minutes
    s.add(meet_patricia_start >= meet_joseph_end + 31)

    # After Patricia, travel to Haight: 15 minutes
    s.add(meet_sarah_start >= meet_patricia_end + 15)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        print(f"Meet Matthew at Marina: from {540 + m[meet_matthew_start].as_long()} to {540 + m[meet_matthew_end].as_long()}")
        print(f"Meet Robert at Union Square: from {540 + m[meet_robert_start].as_long()} to {540 + m[meet_robert_end].as_long()}")
        print(f"Meet Joseph at Financial: from {540 + m[meet_joseph_start].as_long()} to {540 + m[meet_joseph_end].as_long()}")
        print(f"Meet Patricia at Sunset: from {540 + m[meet_patricia_start].as_long()} to {540 + m[meet_patricia_end].as_long()}")
        print(f"Meet Sarah at Haight: from {540 + m[meet_sarah_start].as_long()} to {540 + m[meet_sarah_end].as_long()}")
    else:
        print("No feasible schedule found that meets all constraints.")

if __name__ == "__main__":
    main()
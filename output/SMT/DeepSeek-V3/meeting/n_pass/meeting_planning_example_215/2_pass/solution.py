from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Locations
    Bayview, Embarcadero, Richmond, Fisherman = 0, 1, 2, 3
    locations = ["Bayview", "Embarcadero", "Richmond District", "Fisherman's Wharf"]

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 19, 25, 25],    # Bayview to others
        [21, 0, 21, 6],      # Embarcadero to others
        [26, 19, 0, 18],     # Richmond to others
        [26, 8, 18, 0]       # Fisherman's Wharf to others
    ]

    # Meeting constraints (times in minutes from 9:00 AM)
    # Jessica: Embarcadero, 4:45PM-7:00PM (1050-1200 mins from 9:00 AM), min 30 mins
    jessica_start = 16 * 60 + 45 - 9 * 60  # 4:45 PM is 16:45, 9:00 AM is 9:00
    jessica_end = 19 * 60 - 9 * 60         # 7:00 PM is 19:00
    jessica_min = 30

    # Sandra: Richmond, 6:30PM-9:45PM (1230-1365 mins from 9:00 AM), min 120 mins
    sandra_start = 18 * 60 + 30 - 9 * 60   # 6:30 PM is 18:30
    sandra_end = 21 * 60 + 45 - 9 * 60    # 9:45 PM is 21:45
    sandra_min = 120

    # Jason: Fisherman's Wharf, 4:00PM-4:45PM (1020-1065 mins from 9:00 AM), min 30 mins
    jason_start = 16 * 60 - 9 * 60         # 4:00 PM is 16:00
    jason_end = 16 * 60 + 45 - 9 * 60      # 4:45 PM is 16:45
    jason_min = 30

    # Variables for meeting start and end times
    meet_jessica_start = Int('meet_jessica_start')
    meet_jessica_end = Int('meet_jessica_end')
    meet_sandra_start = Int('meet_sandra_start')
    meet_sandra_end = Int('meet_sandra_end')
    meet_jason_start = Int('meet_jason_start')
    meet_jason_end = Int('meet_jason_end')

    # Variables for location before each meeting
    before_jessica = Int('before_jessica')
    before_sandra = Int('before_sandra')
    before_jason = Int('before_jason')

    # Constraints for meeting times
    # Jessica
    s.add(meet_jessica_start >= jessica_start)
    s.add(meet_jessica_end <= jessica_end)
    s.add(meet_jessica_end - meet_jessica_start >= jessica_min)
    s.add(before_jessica >= 0, before_jessica <= 3)

    # Sandra
    s.add(meet_sandra_start >= sandra_start)
    s.add(meet_sandra_end <= sandra_end)
    s.add(meet_sandra_end - meet_sandra_start >= sandra_min)
    s.add(before_sandra >= 0, before_sandra <= 3)

    # Jason
    s.add(meet_jason_start >= jason_start)
    s.add(meet_jason_end <= jason_end)
    s.add(meet_jason_end - meet_jason_start >= jason_min)
    s.add(before_jason >= 0, before_jason <= 3)

    # Initial location is Bayview (0)
    initial_location = Bayview

    # Constraints for travel times
    # Assume the order is Jason -> Jessica -> Sandra (since Jason's window is earliest)
    s.add(before_jason == initial_location)
    s.add(meet_jason_start >= travel_times[before_jason][Fisherman])

    s.add(before_jessica == Fisherman)
    s.add(meet_jessica_start >= meet_jason_end + travel_times[before_jessica][Embarcadero])

    s.add(before_sandra == Embarcadero)
    s.add(meet_sandra_start >= meet_jessica_end + travel_times[before_sandra][Richmond])

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Jason at Fisherman's Wharf from {m[meet_jason_start].as_long()} to {m[meet_jason_end].as_long()} minutes from 9:00 AM")
        print(f"Meet Jessica at Embarcadero from {m[meet_jessica_start].as_long()} to {m[meet_jessica_end].as_long()} minutes from 9:00 AM")
        print(f"Meet Sandra at Richmond District from {m[meet_sandra_start].as_long()} to {m[meet_sandra_end].as_long()} minutes from 9:00 AM")
    else:
        print("No feasible schedule found.")

solve_scheduling()
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
        [21, 0, 21, 6],     # Embarcadero to others
        [26, 19, 0, 18],    # Richmond to others
        [26, 8, 18, 0]      # Fisherman's Wharf to others
    ]

    # Meeting constraints
    # Jessica: Embarcadero, 4:45PM-7:00PM, min 30 mins
    jessica_start = 9*60 + (4*60 + 45)  # 4:45PM in minutes from 9:00AM
    jessica_end = 9*60 + (7*60)         # 7:00PM in minutes from 9:00AM
    jessica_min = 30

    # Sandra: Richmond, 6:30PM-9:45PM, min 120 mins
    sandra_start = 9*60 + (6*60 + 30)   # 6:30PM in minutes from 9:00AM
    sandra_end = 9*60 + (9*60 + 45)     # 9:45PM in minutes from 9:00AM
    sandra_min = 120

    # Jason: Fisherman's Wharf, 4:00PM-4:45PM, min 30 mins
    jason_start = 9*60 + (4*60)         # 4:00PM in minutes from 9:00AM
    jason_end = 9*60 + (4*60 + 45)      # 4:45PM in minutes from 9:00AM
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
    s.add(before_jessica >= 0, before_jessica <= 3)  # 0-3 represents the 4 locations

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
    # From initial location to first meeting
    # We need to decide the order of meetings, but for simplicity, we'll let Z3 choose
    # We'll assume the order is Jason -> Jessica -> Sandra (since Jason's window is earliest)
    # This is a simplification; a more general approach would consider all permutations

    # Order: Jason -> Jessica -> Sandra
    s.add(before_jason == initial_location)
    s.add(meet_jason_start >= 0 + travel_times[before_jason][Fisherman])

    s.add(before_jessica == Fisherman)
    s.add(meet_jessica_start >= meet_jason_end + travel_times[before_jessica][Embarcadero])

    s.add(before_sandra == Embarcadero)
    s.add(meet_sandra_start >= meet_jessica_end + travel_times[before_sandra][Richmond])

    # Objective: maximize the number of friends met (all three in this case)
    # Since we're trying to meet all, the objective is just to find a feasible schedule

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Jason at Fisherman's Wharf from {m[meet_jason_start].as_long() - 9*60} minutes to {m[meet_jason_end].as_long() - 9*60} minutes")
        print(f"Meet Jessica at Embarcadero from {m[meet_jessica_start].as_long() - 9*60} minutes to {m[meet_jessica_end].as_long() - 9*60} minutes")
        print(f"Meet Sandra at Richmond District from {m[meet_sandra_start].as_long() - 9*60} minutes to {m[meet_sandra_end].as_long() - 9*60} minutes")
    else:
        print("No feasible schedule found.")

solve_scheduling()
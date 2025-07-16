from z3 import *
import itertools

def solve_scheduling():
    s = Optimize()

    # Locations
    locations = ["Bayview", "North Beach", "Fisherman's Wharf", "Haight-Ashbury", "Nob Hill",
                 "Golden Gate Park", "Union Square", "Alamo Square", "Presidio", "Chinatown",
                 "Pacific Heights"]

    # Friends' details: (location, (start_time, end_time), min_duration_minutes)
    friends = {
        "Brian": ("North Beach", (13, 19), 90),
        "Richard": ("Fisherman's Wharf", (11, 12.75), 60),
        "Ashley": ("Haight-Ashbury", (15, 20.5), 90),
        "Elizabeth": ("Nob Hill", (11.75, 18.5), 75),
        "Jessica": ("Golden Gate Park", (20, 21.75), 105),
        "Deborah": ("Union Square", (17.5, 22), 60),
        "Kimberly": ("Alamo Square", (17.5, 21.25), 45),
        "Matthew": ("Presidio", (8.25, 9), 15),
        "Kenneth": ("Chinatown", (13.75, 19.5), 105),
        "Anthony": ("Pacific Heights", (14.25, 16), 30)
    }

    # Complete travel times in minutes (converted to hours in constraints)
    travel_times = {
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Pacific Heights"): 23,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Pacific Heights"): 8,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Chinatown"): 11
    }

    # Variables
    arrival = {loc: Real(f'arrival_{loc}') for loc in locations}
    departure = {loc: Real(f'departure_{loc}') for loc in locations}
    visited = {name: Bool(f'visited_{name}') for name in friends}

    # Initial constraints
    s.add(arrival["Bayview"] == 9.0)  # Start at Bayview at 9:00 AM
    s.add(departure["Bayview"] >= 9.0)

    # Friend meeting constraints
    for name, (loc, (start, end), dur) in friends.items():
        dur_hours = dur / 60.0
        s.add(Implies(visited[name], arrival[loc] >= start))
        s.add(Implies(visited[name], departure[loc] <= end))
        s.add(Implies(visited[name], departure[loc] - arrival[loc] >= dur_hours))
        s.add(Implies(Not(visited[name]), arrival[loc] == -1))
        s.add(Implies(Not(visited[name]), departure[loc] == -1))

    # Sequence constraints
    max_visits = len(friends)
    visit_order = [Int(f'visit_{i}') for i in range(max_visits)]
    visit_time = [Real(f'visit_time_{i}') for i in range(max_visits)]
    visit_loc = [Int(f'visit_loc_{i}') for i in range(max_visits)]

    # Create location to index mapping
    loc_to_idx = {loc: idx for idx, loc in enumerate(locations)}
    friend_locs = [friends[name][0] for name in friends]

    # Visit constraints
    for i in range(max_visits):
        s.add(Or([visit_loc[i] == loc_to_idx[loc] for loc in friend_locs] + [visit_loc[i] == -1]))
        s.add(visit_time[i] >= 0)

    # Path constraints
    for i in range(max_visits - 1):
        s.add(Implies(visit_loc[i] != -1, Or(visit_loc[i+1] != -1, i == max_visits - 2)))
        s.add(visit_time[i+1] >= visit_time[i])

    # Connect visits to arrival/departure times
    for name in friends:
        loc = friends[name][0]
        idx = loc_to_idx[loc]
        s.add(Implies(visited[name], Or([And(visit_loc[i] == idx, 
                                           arrival[loc] == visit_time[i]) 
                                       for i in range(max_visits)])))

    # Travel time constraints
    for i in range(max_visits - 1):
        for loc1 in locations:
            for loc2 in locations:
                if (loc1, loc2) in travel_times:
                    s.add(Implies(And(visit_loc[i] == loc_to_idx[loc1], 
                                 visit_loc[i+1] == loc_to_idx[loc2]),
                               visit_time[i+1] >= visit_time[i] + travel_times[(loc1, loc2)]/60))

    # Objective: maximize number of friends visited
    s.maximize(Sum([If(visited[name], 1, 0) for name in friends]))

    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        visited_count = 0
        for name in friends:
            if is_true(m[visited[name]]):
                visited_count += 1
                loc = friends[name][0]
                a = m[arrival[loc]].as_decimal(3)
                d = m[departure[loc]].as_decimal(3)
                print(f"Meet {name} at {loc} from {a} to {d}")
        print(f"\nTotal friends visited: {visited_count}")
    else:
        print("No feasible schedule found")

solve_scheduling()
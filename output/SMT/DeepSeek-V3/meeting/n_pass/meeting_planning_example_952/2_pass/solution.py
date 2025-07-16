from z3 import *

def solve_scheduling():
    s = Solver()

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

    # Travel times (simplified for brevity; full matrix would be better)
    travel_times = {
        ("Bayview", "North Beach"): 22/60,
        ("Bayview", "Fisherman's Wharf"): 25/60,
        ("Bayview", "Haight-Ashbury"): 19/60,
        ("Bayview", "Nob Hill"): 20/60,
        ("Bayview", "Golden Gate Park"): 22/60,
        ("Bayview", "Union Square"): 18/60,
        ("Bayview", "Alamo Square"): 16/60,
        ("Bayview", "Presidio"): 32/60,
        ("Bayview", "Chinatown"): 19/60,
        ("Bayview", "Pacific Heights"): 23/60,
        # Add other travel times as needed...
    }

    # Variables for arrival and departure times at each location (in hours)
    arrival = {loc: Real(f'arrival_{loc}') for loc in locations}
    departure = {loc: Real(f'departure_{loc}') for loc in locations}

    # Initial constraints: start at Bayview at 9:00 AM
    s.add(arrival["Bayview"] == 9.0)
    s.add(departure["Bayview"] >= 9.0)

    # Constraints for each friend
    for name, (loc, (start, end), dur) in friends.items():
        dur_hours = dur / 60.0  # Convert minutes to hours
        s.add(arrival[loc] >= start)
        s.add(departure[loc] <= end)
        s.add(departure[loc] - arrival[loc] >= dur_hours)

    # Ensure you can't be in two places at the same time
    # For simplicity, assume a linear sequence of visits
    # A more complete solution would model all possible sequences
    visited_locations = [loc for name, (loc, _, _) in friends.items()] + ["Bayview"]
    for i in range(len(visited_locations) - 1):
        loc1 = visited_locations[i]
        loc2 = visited_locations[i+1]
        if (loc1, loc2) in travel_times:
            s.add(arrival[loc2] >= departure[loc1] + travel_times[(loc1, loc2)])

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        for loc in locations:
            if loc in visited_locations:
                a = m[arrival[loc]].as_decimal(3)
                d = m[departure[loc]].as_decimal(3)
                print(f"{loc}: Arrive at {a}, Depart at {d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()
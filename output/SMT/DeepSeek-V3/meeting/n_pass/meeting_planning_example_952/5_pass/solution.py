from z3 import *

def solve_scheduling():
    s = Optimize()

    # Locations and their indices
    locations = ["Bayview", "North Beach", "Fisherman's Wharf", "Haight-Ashbury", "Nob Hill",
                 "Golden Gate Park", "Union Square", "Alamo Square", "Presidio", "Chinatown",
                 "Pacific Heights"]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Friends data: (location, (start_hour, end_hour), min_duration_minutes)
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

    # Travel times in minutes (converted to hours in constraints)
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
        # ... (include all other travel times from the problem)
    }

    # Decision variables
    visit_vars = {name: Bool(f'visit_{name}') for name in friends}
    arrival_vars = {loc: Real(f'arrival_{loc}') for loc in locations}
    departure_vars = {loc: Real(f'departure_{loc}') for loc in locations}

    # Initial constraints
    s.add(arrival_vars["Bayview"] == 9.0)  # Start at Bayview at 9:00 AM
    s.add(departure_vars["Bayview"] >= 9.0)

    # Friend meeting constraints
    for name, (loc, (start, end), dur) in friends.items():
        dur_hours = dur / 60.0
        s.add(Implies(visit_vars[name], arrival_vars[loc] >= start))
        s.add(Implies(visit_vars[name], departure_vars[loc] <= end))
        s.add(Implies(visit_vars[name], departure_vars[loc] - arrival_vars[loc] >= dur_hours))
        s.add(Implies(Not(visit_vars[name]), arrival_vars[loc] == -1))
        s.add(Implies(Not(visit_vars[name]), departure_vars[loc] == -1))

    # Sequence modeling
    max_visits = len(friends)
    visit_order = [Int(f'order_{i}') for i in range(max_visits)]
    visit_time = [Real(f'time_{i}') for i in range(max_visits)]
    visit_location = [Int(f'loc_{i}') for i in range(max_visits)]

    # Visit constraints
    for i in range(max_visits):
        s.add(Or([visit_location[i] == loc_index[loc] for loc in locations] + [visit_location[i] == -1]))
        s.add(visit_time[i] >= 0)

    # Path constraints
    for i in range(max_visits - 1):
        s.add(Implies(visit_location[i] != -1, Or(visit_location[i+1] != -1, i == max_visits - 2)))
        s.add(visit_time[i+1] >= visit_time[i])

    # Connect visits to variables
    for name in friends:
        loc = friends[name][0]
        idx = loc_index[loc]
        s.add(Implies(visit_vars[name], Or([And(visit_location[i] == idx, 
                                              arrival_vars[loc] == visit_time[i]) 
                                          for i in range(max_visits)])))

    # Travel time constraints
    for i in range(max_visits - 1):
        for loc1 in locations:
            for loc2 in locations:
                if (loc1, loc2) in travel_times:
                    s.add(Implies(And(visit_location[i] == loc_index[loc1], 
                                    visit_location[i+1] == loc_index[loc2]),
                               visit_time[i+1] >= visit_time[i] + travel_times[(loc1, loc2)]/60))

    # Objective: maximize number of friends visited
    s.maximize(Sum([If(visit_vars[name], 1, 0) for name in friends]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        print("----------------")
        visited_count = 0
        
        # Collect all visits in chronological order
        schedule = []
        for i in range(max_visits):
            loc_idx = m[visit_location[i]].as_long()
            if loc_idx != -1:
                loc = locations[loc_idx]
                time = m[visit_time[i]].as_decimal(3)
                schedule.append((loc, float(time)))
        
        # Sort by time and print
        schedule.sort(key=lambda x: x[1])
        for loc, time in schedule:
            for name in friends:
                if friends[name][0] == loc and is_true(m[visit_vars[name]]):
                    print(f"{time:.2f}h: Meet {name} at {loc}")
                    visited_count += 1
        
        print(f"\nTotal friends visited: {visited_count}")
    else:
        print("No feasible schedule found")

solve_scheduling()
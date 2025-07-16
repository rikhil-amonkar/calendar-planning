from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Locations
    locations = [
        "Chinatown",
        "Embarcadero",
        "Pacific Heights",
        "Russian Hill",
        "Haight-Ashbury",
        "Golden Gate Park",
        "Fisherman's Wharf",
        "Sunset District",
        "The Castro"
    ]

    # Travel times matrix (in minutes)
    travel_times = {
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "The Castro"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "The Castro"): 17,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Sunset District"): 17
    }

    # Friends' availability and constraints
    friends = {
        "Richard": {"location": "Embarcadero", "start": 15*60 + 15, "end": 18*60 + 45, "min_duration": 90},
        "Mark": {"location": "Pacific Heights", "start": 15*60, "end": 17*60, "min_duration": 45},
        "Matthew": {"location": "Russian Hill", "start": 17*60 + 30, "end": 21*60, "min_duration": 90},
        "Rebecca": {"location": "Haight-Ashbury", "start": 14*60 + 45, "end": 18*60, "min_duration": 60},
        "Melissa": {"location": "Golden Gate Park", "start": 13*60 + 45, "end": 17*60 + 30, "min_duration": 90},
        "Margaret": {"location": "Fisherman's Wharf", "start": 14*60 + 45, "end": 20*60 + 15, "min_duration": 15},
        "Emily": {"location": "Sunset District", "start": 15*60 + 45, "end": 17*60, "min_duration": 45},
        "George": {"location": "The Castro", "start": 14*60, "end": 16*60 + 15, "min_duration": 75}
    }

    # Variables for arrival and departure times at each location
    arrival = {loc: Int(f'arrival_{loc}') for loc in locations}
    departure = {loc: Int(f'departure_{loc}') for loc in locations}

    # Variables to track if we visit each location
    visit = {loc: Bool(f'visit_{loc}') for loc in locations}

    # Initial constraints
    s.add(arrival["Chinatown"] == 540)  # Start at Chinatown at 9:00 AM (540 minutes)
    s.add(departure["Chinatown"] >= arrival["Chinatown"])
    s.add(visit["Chinatown"] == True)

    # Constraints for visiting locations
    for loc in locations:
        # If we visit a location, arrival must be before departure
        s.add(Implies(visit[loc], arrival[loc] <= departure[loc]))
        # If we don't visit, arrival and departure are 0
        s.add(Implies(Not(visit[loc]), arrival[loc] == 0)
        s.add(Implies(Not(visit[loc]), departure[loc] == 0)

    # Friend meeting constraints
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}
    for name, data in friends.items():
        loc = data["location"]
        start = data["start"]
        end = data["end"]
        min_duration = data["min_duration"]

        # To meet a friend, we must visit their location
        s.add(Implies(meet_friend[name], visit[loc]))
        # Meeting time must fit within their availability
        s.add(Implies(meet_friend[name], arrival[loc] <= end - min_duration))
        s.add(Implies(meet_friend[name], departure[loc] >= arrival[loc] + min_duration))
        s.add(Implies(meet_friend[name], arrival[loc] >= start))
        s.add(Implies(meet_friend[name], departure[loc] <= end))

    # Travel constraints
    for loc1 in locations:
        for loc2 in locations:
            if loc1 != loc2 and (loc1, loc2) in travel_times:
                travel_time = travel_times[(loc1, loc2)]
                # If we visit both locations consecutively, respect travel time
                s.add(Implies(And(visit[loc1], visit[loc2]),
                            Or(departure[loc1] <= arrival[loc2] - travel_time,
                               arrival[loc2] <= departure[loc1] - travel_time)))

    # No overlapping visits
    for loc1 in locations:
        for loc2 in locations:
            if loc1 != loc2:
                s.add(Or(Not(visit[loc1]), Not(visit[loc2]),
                         departure[loc1] <= arrival[loc2],
                         departure[loc2] <= arrival[loc1]))

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found. Friends met:")
        met_count = 0
        for name in friends:
            if m.evaluate(meet_friend[name]):
                print(f"- {name} at {friends[name]['location']}")
                met_count += 1
        print(f"\nTotal friends met: {met_count}/{len(friends)}")
        
        # Print detailed schedule
        print("\nDetailed schedule:")
        schedule = []
        for loc in locations:
            if m.evaluate(visit[loc]):
                arr = m.evaluate(arrival[loc]).as_long()
                dep = m.evaluate(departure[loc]).as_long()
                schedule.append((loc, arr, dep))
        
        # Sort schedule by arrival time
        schedule.sort(key=lambda x: x[1])
        
        for loc, arr, dep in schedule:
            print(f"{loc}: {arr//60:02d}:{arr%60:02d} to {dep//60:02d}:{dep%60:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()
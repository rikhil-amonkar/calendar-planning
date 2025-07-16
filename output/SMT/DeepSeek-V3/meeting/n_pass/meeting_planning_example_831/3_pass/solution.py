from z3 import *

def solve_scheduling():
    # Initialize the optimizer
    opt = Optimize()

    # Define friends and their availability (converted to hours)
    friends = {
        "Jeffrey": {"location": "Fisherman's Wharf", "available_start": 10.25, "available_end": 13.0, "min_duration": 1.5},
        "Ronald": {"location": "Alamo Square", "available_start": 7.75, "available_end": 14.75, "min_duration": 2.0},
        "Jason": {"location": "Financial District", "available_start": 10.75, "available_end": 16.0, "min_duration": 1.75},
        "Melissa": {"location": "Union Square", "available_start": 17.75, "available_end": 18.25, "min_duration": 0.25},
        "Elizabeth": {"location": "Sunset District", "available_start": 14.75, "available_end": 17.5, "min_duration": 1.75},
        "Margaret": {"location": "Embarcadero", "available_start": 13.25, "available_end": 19.0, "min_duration": 1.5},
        "George": {"location": "Golden Gate Park", "available_start": 19.0, "available_end": 22.0, "min_duration": 1.25},
        "Richard": {"location": "Chinatown", "available_start": 9.5, "available_end": 21.0, "min_duration": 0.25},
        "Laura": {"location": "Richmond District", "available_start": 9.75, "available_end": 18.0, "min_duration": 1.0}
    }

    # Travel times in hours (from_location, to_location) -> travel time
    travel_times = {
        ("Presidio", "Fisherman's Wharf"): 19/60,
        ("Presidio", "Alamo Square"): 19/60,
        ("Presidio", "Financial District"): 23/60,
        ("Presidio", "Union Square"): 22/60,
        ("Presidio", "Sunset District"): 15/60,
        ("Presidio", "Embarcadero"): 20/60,
        ("Presidio", "Golden Gate Park"): 12/60,
        ("Presidio", "Chinatown"): 21/60,
        ("Presidio", "Richmond District"): 7/60,
        ("Fisherman's Wharf", "Alamo Square"): 21/60,
        ("Fisherman's Wharf", "Financial District"): 11/60,
        ("Fisherman's Wharf", "Union Square"): 13/60,
        ("Fisherman's Wharf", "Embarcadero"): 8/60,
        ("Fisherman's Wharf", "Chinatown"): 12/60,
        ("Alamo Square", "Financial District"): 17/60,
        ("Alamo Square", "Union Square"): 14/60,
        ("Alamo Square", "Golden Gate Park"): 9/60,
        ("Financial District", "Union Square"): 9/60,
        ("Financial District", "Embarcadero"): 4/60,
        ("Financial District", "Chinatown"): 5/60,
        ("Union Square", "Embarcadero"): 11/60,
        ("Union Square", "Chinatown"): 7/60,
        ("Sunset District", "Golden Gate Park"): 11/60,
        ("Embarcadero", "Chinatown"): 7/60,
        ("Golden Gate Park", "Richmond District"): 7/60,
        ("Chinatown", "Richmond District"): 20/60
    }

    # Create variables for meeting times
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}  # Whether we meet each friend

    # Current location starts at Presidio at 9:00 AM
    current_location = "Presidio"
    current_time = 9.0

    # Basic constraints for each friend
    for name in friends:
        friend = friends[name]
        # If we meet this friend, enforce time constraints
        opt.add(Implies(meet_friend[name], 
                       And(meeting_starts[name] >= friend["available_start"],
                           meeting_ends[name] <= friend["available_end"],
                           meeting_ends[name] - meeting_starts[name] >= friend["min_duration"])))

    # Meeting sequence constraints
    all_names = list(friends.keys())
    for i in range(len(all_names)):
        for j in range(i+1, len(all_names)):
            name1 = all_names[i]
            name2 = all_names[j]
            loc1 = friends[name1]["location"]
            loc2 = friends[name2]["location"]
            
            # Get travel time (try both directions)
            travel_time = travel_times.get((loc1, loc2), 
                         travel_times.get((loc2, loc1), 0))
            
            # If we meet both, ensure no overlap with travel time
            opt.add(Implies(And(meet_friend[name1], meet_friend[name2]),
                    Or(meeting_ends[name1] + travel_time <= meeting_starts[name2],
                       meeting_ends[name2] + travel_time <= meeting_starts[name1])))

    # First meeting must be after arrival at Presidio
    for name in friends:
        loc = friends[name]["location"]
        travel_time = travel_times.get(("Presidio", loc), 0)
        opt.add(Implies(meet_friend[name], 
                       meeting_starts[name] >= current_time + travel_time))

    # Try to meet as many friends as possible
    opt.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Then maximize total meeting time
    total_duration = Sum([If(meet_friend[name], 
                         meeting_ends[name] - meeting_starts[name], 0) 
                         for name in friends])
    opt.maximize(total_duration)

    if opt.check() == sat:
        m = opt.model()
        print("Optimal Schedule Found:")
        print(f"Total friends met: {sum(1 for name in friends if is_true(m[meet_friend[name]]))}")
        
        # Sort meetings by start time
        scheduled = [(name, float(m[meeting_starts[name]].as_decimal(10)), 
                    float(m[meeting_ends[name]].as_decimal(10))) 
                    for name in friends if is_true(m[meet_friend[name]])]
        scheduled.sort(key=lambda x: x[1])
        
        current_loc = "Presidio"
        for name, start, end in scheduled:
            loc = friends[name]["location"]
            travel_time = travel_times.get((current_loc, loc), 0)
            print(f"\nTravel from {current_loc} to {loc}: {travel_time*60:.0f} min")
            current_loc = loc
            
            duration = end - start
            print(f"Meet {name} at {loc} from {start:.2f} to {end:.2f} ({duration:.2f} hours)")
    else:
        print("No feasible schedule found (even with relaxed constraints)")

solve_scheduling()
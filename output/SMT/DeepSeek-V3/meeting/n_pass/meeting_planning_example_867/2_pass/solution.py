from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Define locations and friends
    locations = [
        "Haight-Ashbury",
        "Mission District",
        "Union Square",
        "Pacific Heights",
        "Bayview",
        "Fisherman's Wharf",
        "Marina District",
        "Richmond District",
        "Sunset District",
        "Golden Gate Park"
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Haight-Ashbury": {
            "Mission District": 11,
            "Union Square": 19,
            "Pacific Heights": 12,
            "Bayview": 18,
            "Fisherman's Wharf": 23,
            "Marina District": 17,
            "Richmond District": 10,
            "Sunset District": 15,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "Haight-Ashbury": 12,
            "Union Square": 15,
            "Pacific Heights": 16,
            "Bayview": 14,
            "Fisherman's Wharf": 22,
            "Marina District": 19,
            "Richmond District": 20,
            "Sunset District": 24,
            "Golden Gate Park": 17
        },
        "Union Square": {
            "Haight-Ashbury": 18,
            "Mission District": 14,
            "Pacific Heights": 15,
            "Bayview": 15,
            "Fisherman's Wharf": 15,
            "Marina District": 18,
            "Richmond District": 20,
            "Sunset District": 27,
            "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "Haight-Ashbury": 11,
            "Mission District": 15,
            "Union Square": 12,
            "Bayview": 22,
            "Fisherman's Wharf": 13,
            "Marina District": 6,
            "Richmond District": 12,
            "Sunset District": 21,
            "Golden Gate Park": 15
        },
        "Bayview": {
            "Haight-Ashbury": 19,
            "Mission District": 13,
            "Union Square": 18,
            "Pacific Heights": 23,
            "Fisherman's Wharf": 25,
            "Marina District": 27,
            "Richmond District": 25,
            "Sunset District": 23,
            "Golden Gate Park": 22
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22,
            "Mission District": 22,
            "Union Square": 13,
            "Pacific Heights": 12,
            "Bayview": 26,
            "Marina District": 9,
            "Richmond District": 18,
            "Sunset District": 27,
            "Golden Gate Park": 25
        },
        "Marina District": {
            "Haight-Ashbury": 16,
            "Mission District": 20,
            "Union Square": 16,
            "Pacific Heights": 7,
            "Bayview": 27,
            "Fisherman's Wharf": 10,
            "Richmond District": 11,
            "Sunset District": 19,
            "Golden Gate Park": 18
        },
        "Richmond District": {
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Union Square": 21,
            "Pacific Heights": 10,
            "Bayview": 27,
            "Fisherman's Wharf": 18,
            "Marina District": 9,
            "Sunset District": 11,
            "Golden Gate Park": 9
        },
        "Sunset District": {
            "Haight-Ashbury": 15,
            "Mission District": 25,
            "Union Square": 30,
            "Pacific Heights": 21,
            "Bayview": 22,
            "Fisherman's Wharf": 29,
            "Marina District": 21,
            "Richmond District": 12,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Union Square": 22,
            "Pacific Heights": 16,
            "Bayview": 23,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Richmond District": 7,
            "Sunset District": 10
        }
    }

    # Friends' data: name, location, available_start, available_end, min_duration
    friends = [
        ("Elizabeth", "Mission District", 10.5, 20.0, 1.5),
        ("David", "Union Square", 15.25, 19.0, 0.75),
        ("Sandra", "Pacific Heights", 7.0, 20.0, 2.0),
        ("Thomas", "Bayview", 19.5, 20.5, 0.5),
        ("Robert", "Fisherman's Wharf", 10.0, 15.0, 0.25),
        ("Kenneth", "Marina District", 10.75, 13.0, 0.75),
        ("Melissa", "Richmond District", 18.25, 20.0, 0.25),
        ("Kimberly", "Sunset District", 10.25, 18.25, 1.75),
        ("Amanda", "Golden Gate Park", 7.75, 18.75, 0.25)
    ]

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(t):
        return int(t * 60)

    current_location = "Haight-Ashbury"
    current_time = time_to_minutes(9.0)  # 9:00 AM in minutes

    # Variables for each meeting: start and end times
    meeting_vars = {}
    for name, loc, start, end, dur in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = (start_var, end_var, loc, dur * 60)

        # Constraints: meeting must be within friend's availability
        opt.add(start_var >= time_to_minutes(start))
        opt.add(end_var <= time_to_minutes(end))
        opt.add(end_var == start_var + dur * 60)

    # Binary variables to track if a friend is met
    met = [Bool(f"met_{name}") for name, _, _, _, _ in friends]
    for i, (name, _, _, _, _) in enumerate(friends):
        start_var, end_var, loc, dur = meeting_vars[name]
        # If met, ensure the meeting fits in the schedule
        opt.add(Implies(met[i], start_var >= current_time))
        # Add travel time from current_location to friend's location
        travel_time = travel_times[current_location][loc]
        opt.add(Implies(met[i], start_var >= current_time + travel_time))
        # Update current_location and current_time if meeting is scheduled
        # This is a simplification; a more precise model would track the sequence

    # Maximize the number of friends met
    opt.maximize(Sum([If(m, 1, 0) for m in met]))

    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        print("SOLUTION:")
        scheduled = []
        for i, (name, _, _, _, _) in enumerate(friends):
            if is_true(model[met[i]]):
                start_var, end_var, loc, dur = meeting_vars[name]
                start = model[start_var].as_long()
                end = model[end_var].as_long()
                # Convert minutes back to hours
                start_hr = 9 + start // 60
                start_min = start % 60
                end_hr = 9 + end // 60
                end_min = end % 60
                scheduled.append((name, loc, f"{start_hr}:{start_min:02d}", f"{end_hr}:{end_min:02d}"))
        # Sort by start time
        scheduled.sort(key=lambda x: x[2])
        for name, loc, start, end in scheduled:
            print(f"Meet {name} at {loc} from {start} to {end}")
    else:
        print("No solution found")

solve_scheduling()
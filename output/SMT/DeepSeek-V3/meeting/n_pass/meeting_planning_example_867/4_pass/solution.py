from z3 import *

def solve_scheduling():
    opt = Optimize()

    # Define all locations
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

    # Complete travel times dictionary
    travel_times = {
        "Haight-Ashbury": {
            "Mission District": 11, "Union Square": 19, "Pacific Heights": 12,
            "Bayview": 18, "Fisherman's Wharf": 23, "Marina District": 17,
            "Richmond District": 10, "Sunset District": 15, "Golden Gate Park": 7
        },
        "Mission District": {
            "Haight-Ashbury": 12, "Union Square": 15, "Pacific Heights": 16,
            "Bayview": 14, "Fisherman's Wharf": 22, "Marina District": 19,
            "Richmond District": 20, "Sunset District": 24, "Golden Gate Park": 17
        },
        "Union Square": {
            "Haight-Ashbury": 18, "Mission District": 14, "Pacific Heights": 15,
            "Bayview": 15, "Fisherman's Wharf": 15, "Marina District": 18,
            "Richmond District": 20, "Sunset District": 27, "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "Haight-Ashbury": 11, "Mission District": 15, "Union Square": 12,
            "Bayview": 22, "Fisherman's Wharf": 13, "Marina District": 6,
            "Richmond District": 12, "Sunset District": 21, "Golden Gate Park": 15
        },
        "Bayview": {
            "Haight-Ashbury": 19, "Mission District": 13, "Union Square": 18,
            "Pacific Heights": 23, "Fisherman's Wharf": 25, "Marina District": 27,
            "Richmond District": 25, "Sunset District": 23, "Golden Gate Park": 22
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22, "Mission District": 22, "Union Square": 13,
            "Pacific Heights": 12, "Bayview": 26, "Marina District": 9,
            "Richmond District": 18, "Sunset District": 27, "Golden Gate Park": 25
        },
        "Marina District": {
            "Haight-Ashbury": 16, "Mission District": 20, "Union Square": 16,
            "Pacific Heights": 7, "Bayview": 27, "Fisherman's Wharf": 10,
            "Richmond District": 11, "Sunset District": 19, "Golden Gate Park": 18
        },
        "Richmond District": {
            "Haight-Ashbury": 10, "Mission District": 20, "Union Square": 21,
            "Pacific Heights": 10, "Bayview": 27, "Fisherman's Wharf": 18,
            "Marina District": 9, "Sunset District": 11, "Golden Gate Park": 9
        },
        "Sunset District": {
            "Haight-Ashbury": 15, "Mission District": 25, "Union Square": 30,
            "Pacific Heights": 21, "Bayview": 22, "Fisherman's Wharf": 29,
            "Marina District": 21, "Richmond District": 12, "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Haight-Ashbury": 7, "Mission District": 17, "Union Square": 22,
            "Pacific Heights": 16, "Bayview": 23, "Fisherman's Wharf": 24,
            "Marina District": 16, "Richmond District": 7, "Sunset District": 10
        }
    }

    # Friends' data
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

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(t):
        return int(t * 60)

    # Variables
    meeting_start = {name: Int(f"start_{name}") for name, _, _, _, _ in friends}
    meeting_end = {name: Int(f"end_{name}") for name, _, _, _, _ in friends}
    is_met = {name: Bool(f"met_{name}") for name, _, _, _, _ in friends}

    # Constraints for each friend
    for name, loc, start, end, dur in friends:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        dur_min = int(dur * 60)
        
        opt.add(Implies(is_met[name], meeting_start[name] >= start_min))
        opt.add(Implies(is_met[name], meeting_end[name] <= end_min))
        opt.add(Implies(is_met[name], meeting_end[name] == meeting_start[name] + dur_min))

    # No overlapping meetings and travel time constraints
    for i, (name1, loc1, _, _, _) in enumerate(friends):
        for j, (name2, loc2, _, _, _) in enumerate(friends):
            if i != j:
                travel_time = travel_times[loc1][loc2]
                opt.add(Implies(And(is_met[name1], is_met[name2]),
                              Or(meeting_end[name1] + travel_time <= meeting_start[name2],
                                 meeting_end[name2] + travel_times[loc2][loc1] <= meeting_start[name1]))

    # Starting at Haight-Ashbury at 9:00 AM (540 minutes)
    first_meeting_constraints = []
    for name, loc, _, _, _ in friends:
        first_meeting_constraints.append(
            And(is_met[name], meeting_start[name] >= 540 + travel_times["Haight-Ashbury"][loc])
        )
    opt.add(Or(first_meeting_constraints))

    # Maximize number of friends met
    opt.maximize(Sum([If(is_met[name], 1, 0) for name, _, _, _, _ in friends]))

    if opt.check() == sat:
        model = opt.model()
        print("SOLUTION:")
        scheduled = []
        for name, loc, _, _, _ in friends:
            if is_true(model[is_met[name]]):
                start = model[meeting_start[name]].as_long()
                end = model[meeting_end[name]].as_long()
                start_hr = 9 + start // 60
                start_min = start % 60
                end_hr = 9 + end // 60
                end_min = end % 60
                scheduled.append((name, loc, f"{start_hr}:{start_min:02d}", f"{end_hr}:{end_min:02d}"))
        
        scheduled.sort(key=lambda x: x[2])
        for name, loc, start, end in scheduled:
            print(f"Meet {name} at {loc} from {start} to {end}")
    else:
        print("No valid schedule found")

solve_scheduling()
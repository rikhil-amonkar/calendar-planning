from z3 import *

def solve_scheduling():
    opt = Optimize()

    # Locations and travel times (in minutes)
    locations = ["Haight-Ashbury", "Mission District", "Union Square", "Pacific Heights", 
                 "Bayview", "Fisherman's Wharf", "Marina District", "Richmond District", 
                 "Sunset District", "Golden Gate Park"]

    travel_times = {
        "Haight-Ashbury": {"Mission District": 11, "Union Square": 19, "Pacific Heights": 12, 
                           "Bayview": 18, "Fisherman's Wharf": 23, "Marina District": 17, 
                           "Richmond District": 10, "Sunset District": 15, "Golden Gate Park": 7},
        # ... (other travel times remain the same as previous solution)
    }

    # Friends' data: (name, location, available_start, available_end, min_duration in hours)
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
                # Either meeting1 is before meeting2 (with travel time) or vice versa
                opt.add(Implies(And(is_met[name1], is_met[name2]),
                              Or(meeting_end[name1] + travel_times[loc1][loc2] <= meeting_start[name2],
                                 meeting_end[name2] + travel_times[loc2][loc1] <= meeting_start[name1])))

    # Starting at Haight-Ashbury at 9:00 AM (540 minutes)
    opt.add(Or([And(is_met[name], meeting_start[name] >= 540 + travel_times["Haight-Ashbury"][loc]) 
               for name, loc, _, _, _ in friends]))

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
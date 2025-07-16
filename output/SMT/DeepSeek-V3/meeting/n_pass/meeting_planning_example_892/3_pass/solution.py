from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define districts and travel times
    districts = ["Marina District", "Bayview", "Sunset District", "Richmond District",
                "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach",
                "Russian Hill", "Embarcadero"]

    # Travel times in minutes between districts
    travel_times = {
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Embarcadero"): 14,
        # ... (include all other travel times from the original problem)
    }

    # Friends and their availability
    friends = {
        "Charles": {"district": "Bayview", "start": 11.5, "end": 14.5, "duration": 0.75},
        "Robert": {"district": "Sunset District", "start": 16.75, "end": 21.0, "duration": 0.5},
        "Karen": {"district": "Richmond District", "start": 19.25, "end": 21.5, "duration": 1.0},
        "Rebecca": {"district": "Nob Hill", "start": 16.25, "end": 20.5, "duration": 1.5},
        "Margaret": {"district": "Chinatown", "start": 14.25, "end": 19.75, "duration": 2.0},
        "Patricia": {"district": "Haight-Ashbury", "start": 14.5, "end": 20.5, "duration": 0.75},
        "Mark": {"district": "North Beach", "start": 14.0, "end": 18.5, "duration": 1.75},
        "Melissa": {"district": "Russian Hill", "start": 13.0, "end": 19.75, "duration": 0.5},
        "Laura": {"district": "Embarcadero", "start": 7.75, "end": 13.25, "duration": 1.75},
    }

    # Create variables for each meeting
    meet = {name: Bool(f"meet_{name}") for name in friends}
    start_time = {name: Real(f"start_{name}") for name in friends}
    end_time = {name: Real(f"end_{name}") for name in friends}

    # Meeting duration constraints
    for name in friends:
        s.add(Implies(meet[name], 
                     And(start_time[name] >= friends[name]["start"],
                         end_time[name] <= friends[name]["end"],
                         end_time[name] - start_time[name] >= friends[name]["duration"])))

    # Initial conditions
    current_time = 9.0  # Start at 9:00 AM
    current_district = "Marina District"

    # Create meeting order variables
    order = {name: Int(f"order_{name}") for name in friends}
    max_order = len(friends)
    for name in friends:
        s.add(Or(order[name] == -1, And(order[name] >= 0, order[name] < max_order)))

    # All active meetings must have unique order positions
    active_orders = [If(meet[name], order[name], -1) for name in friends]
    s.add(Distinct([o for o in active_orders if o != -1]))

    # Travel time constraints between consecutive meetings
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            s.add(Implies(
                And(meet[name1], meet[name2], order[name1] >= 0, order[name2] >= 0, order[name1] + 1 == order[name2]),
                start_time[name2] >= end_time[name1] + travel_times.get(
                    (friends[name1]["district"], friends[name2]["district"]), 0) / 60
            ))

    # First meeting must be after initial time plus travel time
    for name in friends:
        s.add(Implies(
            And(meet[name], order[name] == 0),
            start_time[name] >= current_time + travel_times.get(
                (current_district, friends[name]["district"]), 0) / 60
        ))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Collect scheduled meetings
        scheduled = []
        for name in friends:
            if m.evaluate(meet[name]):
                o = m.evaluate(order[name])
                st = m.evaluate(start_time[name])
                et = m.evaluate(end_time[name])
                scheduled.append((o, name, st, et))
        
        # Sort by order and print
        scheduled.sort()
        for o, name, st, et in scheduled:
            print(f"{o+1}. Meet {name} at {friends[name]['district']} from {st:.2f} to {et:.2f}")
    else:
        print("No valid schedule found")

solve_scheduling()
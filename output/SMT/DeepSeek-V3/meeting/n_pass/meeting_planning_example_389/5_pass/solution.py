from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define locations and travel times (in minutes)
    locations = ["Haight-Ashbury", "Fisherman's Wharf", "Richmond District", "Mission District", "Bayview"]
    travel = {
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Bayview"): 26,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Bayview"): 15,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Mission District"): 13,
    }

    # Friend availability (converted to minutes since midnight)
    friends = {
        "Sarah": {"location": "Fisherman's Wharf", "start": 14*60+45, "end": 17*60+30, "min_duration": 105},
        "Mary": {"location": "Richmond District", "start": 13*60, "end": 19*60+15, "min_duration": 75},
        "Helen": {"location": "Mission District", "start": 21*60+45, "end": 22*60+30, "min_duration": 30},
        "Thomas": {"location": "Bayview", "start": 15*60+15, "end": 18*60+45, "min_duration": 120}
    }

    # Decision variables
    meet_vars = {name: Bool(f"meet_{name}") for name in friends}
    start_vars = {name: Int(f"start_{name}") for name in friends}
    end_vars = {name: Int(f"end_{name}") for name in friends}
    order_vars = {name: Int(f"order_{name}") for name in friends}

    # Current time starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_loc = "Haight-Ashbury"

    # Basic constraints for each friend
    for name in friends:
        info = friends[name]
        s.add(Implies(meet_vars[name], start_vars[name] >= info["start"]))
        s.add(Implies(meet_vars[name], end_vars[name] <= info["end"]))
        s.add(Implies(meet_vars[name], end_vars[name] - start_vars[name] >= info["min_duration"]))
        s.add(Implies(meet_vars[name], order_vars[name] >= 1))
        s.add(Implies(Not(meet_vars[name]), order_vars[name] == 0))

    # Ensure unique ordering for meetings that happen
    active_orders = [order_vars[name] for name in friends if name != "Helen"]
    s.add(Distinct([o for o in active_orders if o != 0]))  # Filter out zeros

    # Travel time constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                src = friends[name1]["location"]
                dst = friends[name2]["location"]
                travel_time = travel.get((src, dst), 0)
                s.add(Implies(
                    And(meet_vars[name1], meet_vars[name2], order_vars[name1] < order_vars[name2]),
                    start_vars[name2] >= end_vars[name1] + travel_time
                ))

    # Initial travel from Haight-Ashbury to first meeting
    for name in friends:
        dst = friends[name]["location"]
        travel_time = travel.get((current_loc, dst), 0)
        s.add(Implies(
            And(meet_vars[name], order_vars[name] == 1),
            start_vars[name] >= current_time + travel_time
        ))

    # Helen must be last if met
    for name in friends:
        if name != "Helen":
            s.add(Implies(
                And(meet_vars[name], meet_vars["Helen"]),
                order_vars[name] < order_vars["Helen"]
            ))

    # Objective: maximize number of friends met
    num_met = Int("num_met")
    s.add(num_met == Sum([If(meet_vars[name], 1, 0) for name in friends]))
    s.maximize(num_met)

    # Solve with timeout
    s.set("timeout", 30000)  # 30 second timeout
    result = s.check()

    if result == sat:
        m = s.model()
        num_met_val = m.evaluate(num_met).as_long()
        print("SOLUTION:")
        print(f"Number of friends met: {num_met_val}")
        
        # Get meetings in order
        meetings = []
        for name in friends:
            if is_true(m.evaluate(meet_vars[name])):
                order = m.evaluate(order_vars[name]).as_long()
                start = m.evaluate(start_vars[name]).as_long()
                end = m.evaluate(end_vars[name]).as_long()
                meetings.append((order, name, start, end))
        
        # Sort by order
        meetings.sort()
        
        # Print schedule
        current_time = 9 * 60
        current_loc = "Haight-Ashbury"
        for order, name, start, end in meetings:
            dst = friends[name]["location"]
            travel_time = travel.get((current_loc, dst), 0)
            print(f"Travel from {current_loc} to {dst}: {travel_time} minutes (depart {current_time//60:02d}:{current_time%60:02d})")
            print(f"Meet {name} at {dst} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
            current_time = end
            current_loc = dst
    elif result == unknown:
        print("Solution not found within time limit")
    else:
        print("No feasible schedule found")

solve_scheduling()
from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define districts
    districts = ["Marina District", "Bayview", "Sunset District", "Richmond District",
                "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach",
                "Russian Hill", "Embarcadero"]

    # Travel times in minutes between districts (simplified for this example)
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

    # Create variables
    meet = {name: Bool(f"meet_{name}") for name in friends}
    start_time = {name: Real(f"start_{name}") for name in friends}
    end_time = {name: Real(f"end_{name}") for name in friends}

    # Meeting constraints
    for name in friends:
        s.add(Implies(meet[name], 
                     And(start_time[name] >= friends[name]["start"],
                         end_time[name] <= friends[name]["end"],
                         end_time[name] - start_time[name] >= friends[name]["duration"])))

    # Initial conditions
    current_time = 9.0  # Start at 9:00 AM
    current_district = "Marina District"

    # Create a simple sequence constraint (visit at most one friend at a time)
    # This is a simplified approach to avoid complex ordering constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Implies(And(meet[name1], meet[name2]),
                            Or(end_time[name1] <= start_time[name2],
                               end_time[name2] <= start_time[name1])))

    # Travel time constraints (simplified)
    for name in friends:
        if friends[name]["district"] != current_district:
            travel_time = travel_times.get((current_district, friends[name]["district"]), 0)
            s.add(Implies(meet[name], 
                         start_time[name] >= current_time + travel_time/60))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        # Collect all scheduled meetings
        scheduled = []
        for name in friends:
            if is_true(m.evaluate(meet[name])):
                st = m.evaluate(start_time[name])
                et = m.evaluate(end_time[name])
                scheduled.append((float(st.numerator_as_long())/float(st.denominator_as_long()),
                                float(et.numerator_as_long())/float(et.denominator_as_long()),
                                name))
        
        # Sort by start time and print
        scheduled.sort()
        for idx, (st, et, name) in enumerate(scheduled):
            print(f"{idx+1}. Meet {name} at {friends[name]['district']} from {st:.2f} to {et:.2f}")
    else:
        print("No valid schedule found")

solve_scheduling()
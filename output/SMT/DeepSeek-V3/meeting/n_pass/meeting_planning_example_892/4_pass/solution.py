from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define districts
    districts = ["Marina District", "Bayview", "Sunset District", "Richmond District",
                "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach",
                "Russian Hill", "Embarcadero"]

    # Complete travel times matrix (minutes between districts)
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
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Embarcadero"): 19,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Embarcadero"): 30,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Embarcadero"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Embarcadero"): 6,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8,
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
    start = {name: Real(f"start_{name}") for name in friends}
    end = {name: Real(f"end_{name}") for name in friends}
    order = {name: Int(f"order_{name}") for name in friends}
    max_order = len(friends)

    # Basic constraints
    for name in friends:
        s.add(Implies(meet[name], And(
            start[name] >= friends[name]["start"],
            end[name] <= friends[name]["end"],
            end[name] - start[name] >= friends[name]["duration"],
            order[name] >= 0,
            order[name] < max_order
        )))
        s.add(Implies(Not(meet[name]), order[name] == -1))

    # Order uniqueness
    s.add(Distinct([order[name] for name in friends if meet[name]]))

    # Travel time constraints
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            s.add(Implies(
                And(meet[name1], meet[name2], order[name1] + 1 == order[name2]),
                start[name2] >= end[name1] + travel_times[
                    (friends[name1]["district"], friends[name2]["district"])
                ] / 60
            ))

    # Initial condition (starting at Marina District at 9:00 AM)
    for name in friends:
        s.add(Implies(
            And(meet[name], order[name] == 0),
            start[name] >= 9.0 + travel_times[
                ("Marina District", friends[name]["district"])
            ] / 60 if ("Marina District", friends[name]["district"]) in travel_times else 0
        ))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        scheduled = []
        for name in friends:
            if m.evaluate(meet[name]):
                o = m.evaluate(order[name])
                st = m.evaluate(start[name])
                et = m.evaluate(end[name])
                scheduled.append((o, name, st, et))
        
        scheduled.sort()
        for idx, (o, name, st, et) in enumerate(scheduled):
            print(f"{idx+1}. Meet {name} at {friends[name]['district']} from {float(st):.2f} to {float(et):.2f}")
    else:
        print("No valid schedule found")

solve_scheduling()
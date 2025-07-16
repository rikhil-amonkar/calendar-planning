from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define the districts
    districts = [
        "Marina District", "Bayview", "Sunset District", "Richmond District",
        "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach",
        "Russian Hill", "Embarcadero"
    ]
    
    # Travel times matrix (from district i to district j)
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

    # Friends and their constraints
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

    # Variables for meeting start and end times
    meeting_start = {name: Real(f"start_{name}") for name in friends}
    meeting_end = {name: Real(f"end_{name}") for name in friends}

    # Variables for whether a friend is met
    meet_friend = {name: Bool(f"meet_{name}") for name in friends}

    # Initial constraints: meeting times must be within friend's availability
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet_friend[name], And(
            meeting_start[name] >= friend["start"],
            meeting_end[name] <= friend["end"],
            meeting_end[name] - meeting_start[name] >= friend["duration"]
        )))

    # Initial position and time
    current_district = "Marina District"
    current_time = 9.0

    # Create a list of all possible meetings in order
    all_meetings = list(friends.keys())
    
    # Variables to track the order of meetings
    meeting_order = {name: Int(f"order_{name}") for name in friends}
    for name in friends:
        s.add(Or(meeting_order[name] == -1, And(meeting_order[name] >= 0, meeting_order[name] < len(friends))))
    
    # All active meetings must have unique order positions
    active_orders = [If(meet_friend[name], meeting_order[name], -1) for name in friends]
    s.add(Distinct([o for o in active_orders if o != -1]))

    # Track the current district and time after each meeting
    prev_district = current_district
    prev_time = current_time

    # Constraints for travel times between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            # If both meetings are active and name1 comes before name2
            s.add(Implies(And(meet_friend[name1], meet_friend[name2], meeting_order[name1] < meeting_order[name2]),
                          meeting_start[name2] >= meeting_end[name1] + travel_times[(friends[name1]["district"], friends[name2]["district"])] / 60))

    # Laura is the first meeting (if met) since she's available earliest
    s.add(Implies(meet_friend["Laura"], meeting_order["Laura"] == 0))

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Sort meetings by their order
        scheduled_meetings = []
        for name in friends:
            if m.evaluate(meet_friend[name]):
                order = m.evaluate(meeting_order[name])
                start = m.evaluate(meeting_start[name])
                end = m.evaluate(meeting_end[name])
                scheduled_meetings.append((order, name, start, end))
        
        # Print meetings in order
        scheduled_meetings.sort()
        for order, name, start, end in scheduled_meetings:
            print(f"{order+1}. Meet {name} at {friends[name]['district']} from {start} to {end}")
    else:
        print("No solution found")

solve_scheduling()
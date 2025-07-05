from z3 import *

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Locations
    locations = [
        "Union Square",
        "Presidio",
        "Alamo Square",
        "Marina District",
        "Financial District",
        "Nob Hill",
        "Sunset District",
        "Chinatown",
        "Russian Hill",
        "North Beach",
        "Haight-Ashbury"
    ]

    # Friends and their constraints
    friends = {
        "Kimberly": {"location": "Presidio", "start": 15.5, "end": 16.0, "min_duration": 0.25},
        "Elizabeth": {"location": "Alamo Square", "start": 19.25, "end": 20.25, "min_duration": 0.25},
        "Joshua": {"location": "Marina District", "start": 10.5, "end": 14.25, "min_duration": 0.75},
        "Sandra": {"location": "Financial District", "start": 19.5, "end": 20.25, "min_duration": 0.75},
        "Kenneth": {"location": "Nob Hill", "start": 12.75, "end": 21.75, "min_duration": 0.5},
        "Betty": {"location": "Sunset District", "start": 14.0, "end": 19.0, "min_duration": 1.0},
        "Deborah": {"location": "Chinatown", "start": 17.25, "end": 20.5, "min_duration": 0.25},
        "Barbara": {"location": "Russian Hill", "start": 17.5, "end": 21.25, "min_duration": 2.0},
        "Steven": {"location": "North Beach", "start": 17.75, "end": 20.75, "min_duration": 1.5},
        "Daniel": {"location": "Haight-Ashbury", "start": 18.5, "end": 18.75, "min_duration": 0.25}
    }

    # Travel times (in hours)
    travel_times = {
        ("Union Square", "Presidio"): 24/60,
        ("Union Square", "Alamo Square"): 15/60,
        ("Union Square", "Marina District"): 18/60,
        ("Union Square", "Financial District"): 9/60,
        ("Union Square", "Nob Hill"): 9/60,
        ("Union Square", "Sunset District"): 27/60,
        ("Union Square", "Chinatown"): 7/60,
        ("Union Square", "Russian Hill"): 13/60,
        ("Union Square", "North Beach"): 10/60,
        ("Union Square", "Haight-Ashbury"): 18/60,
        ("Presidio", "Union Square"): 22/60,
        ("Presidio", "Alamo Square"): 19/60,
        ("Presidio", "Marina District"): 11/60,
        ("Presidio", "Financial District"): 23/60,
        ("Presidio", "Nob Hill"): 18/60,
        ("Presidio", "Sunset District"): 15/60,
        ("Presidio", "Chinatown"): 21/60,
        ("Presidio", "Russian Hill"): 14/60,
        ("Presidio", "North Beach"): 18/60,
        ("Presidio", "Haight-Ashbury"): 15/60,
        ("Alamo Square", "Union Square"): 14/60,
        ("Alamo Square", "Presidio"): 17/60,
        ("Alamo Square", "Marina District"): 15/60,
        ("Alamo Square", "Financial District"): 17/60,
        ("Alamo Square", "Nob Hill"): 11/60,
        ("Alamo Square", "Sunset District"): 16/60,
        ("Alamo Square", "Chinatown"): 15/60,
        ("Alamo Square", "Russian Hill"): 13/60,
        ("Alamo Square", "North Beach"): 15/60,
        ("Alamo Square", "Haight-Ashbury"): 5/60,
        ("Marina District", "Union Square"): 16/60,
        ("Marina District", "Presidio"): 10/60,
        ("Marina District", "Alamo Square"): 15/60,
        ("Marina District", "Financial District"): 17/60,
        ("Marina District", "Nob Hill"): 12/60,
        ("Marina District", "Sunset District"): 19/60,
        ("Marina District", "Chinatown"): 15/60,
        ("Marina District", "Russian Hill"): 8/60,
        ("Marina District", "North Beach"): 11/60,
        ("Marina District", "Haight-Ashbury"): 16/60,
        ("Financial District", "Union Square"): 9/60,
        ("Financial District", "Presidio"): 22/60,
        ("Financial District", "Alamo Square"): 17/60,
        ("Financial District", "Marina District"): 15/60,
        ("Financial District", "Nob Hill"): 8/60,
        ("Financial District", "Sunset District"): 30/60,
        ("Financial District", "Chinatown"): 5/60,
        ("Financial District", "Russian Hill"): 11/60,
        ("Financial District", "North Beach"): 7/60,
        ("Financial District", "Haight-Ashbury"): 19/60,
        ("Nob Hill", "Union Square"): 7/60,
        ("Nob Hill", "Presidio"): 17/60,
        ("Nob Hill", "Alamo Square"): 11/60,
        ("Nob Hill", "Marina District"): 11/60,
        ("Nob Hill", "Financial District"): 9/60,
        ("Nob Hill", "Sunset District"): 24/60,
        ("Nob Hill", "Chinatown"): 6/60,
        ("Nob Hill", "Russian Hill"): 5/60,
        ("Nob Hill", "North Beach"): 8/60,
        ("Nob Hill", "Haight-Ashbury"): 13/60,
        ("Sunset District", "Union Square"): 30/60,
        ("Sunset District", "Presidio"): 16/60,
        ("Sunset District", "Alamo Square"): 17/60,
        ("Sunset District", "Marina District"): 21/60,
        ("Sunset District", "Financial District"): 30/60,
        ("Sunset District", "Nob Hill"): 27/60,
        ("Sunset District", "Chinatown"): 30/60,
        ("Sunset District", "Russian Hill"): 24/60,
        ("Sunset District", "North Beach"): 28/60,
        ("Sunset District", "Haight-Ashbury"): 15/60,
        ("Chinatown", "Union Square"): 7/60,
        ("Chinatown", "Presidio"): 19/60,
        ("Chinatown", "Alamo Square"): 17/60,
        ("Chinatown", "Marina District"): 12/60,
        ("Chinatown", "Financial District"): 5/60,
        ("Chinatown", "Nob Hill"): 9/60,
        ("Chinatown", "Sunset District"): 29/60,
        ("Chinatown", "Russian Hill"): 7/60,
        ("Chinatown", "North Beach"): 3/60,
        ("Chinatown", "Haight-Ashbury"): 19/60,
        ("Russian Hill", "Union Square"): 10/60,
        ("Russian Hill", "Presidio"): 14/60,
        ("Russian Hill", "Alamo Square"): 15/60,
        ("Russian Hill", "Marina District"): 7/60,
        ("Russian Hill", "Financial District"): 11/60,
        ("Russian Hill", "Nob Hill"): 5/60,
        ("Russian Hill", "Sunset District"): 23/60,
        ("Russian Hill", "Chinatown"): 9/60,
        ("Russian Hill", "North Beach"): 5/60,
        ("Russian Hill", "Haight-Ashbury"): 17/60,
        ("North Beach", "Union Square"): 7/60,
        ("North Beach", "Presidio"): 17/60,
        ("North Beach", "Alamo Square"): 16/60,
        ("North Beach", "Marina District"): 9/60,
        ("North Beach", "Financial District"): 8/60,
        ("North Beach", "Nob Hill"): 7/60,
        ("North Beach", "Sunset District"): 27/60,
        ("North Beach", "Chinatown"): 6/60,
        ("North Beach", "Russian Hill"): 4/60,
        ("North Beach", "Haight-Ashbury"): 18/60,
        ("Haight-Ashbury", "Union Square"): 19/60,
        ("Haight-Ashbury", "Presidio"): 15/60,
        ("Haight-Ashbury", "Alamo Square"): 5/60,
        ("Haight-Ashbury", "Marina District"): 17/60,
        ("Haight-Ashbury", "Financial District"): 21/60,
        ("Haight-Ashbury", "Nob Hill"): 15/60,
        ("Haight-Ashbury", "Sunset District"): 15/60,
        ("Haight-Ashbury", "Chinatown"): 19/60,
        ("Haight-Ashbury", "Russian Hill"): 17/60,
        ("Haight-Ashbury", "North Beach"): 19/60
    }

    # Decision variables: whether to meet each friend
    meet = {name: Bool(f"meet_{name}") for name in friends}

    # Variables for each friend: arrival and departure times (if met)
    arrival = {name: Real(f"arrival_{name}") for name in friends}
    departure = {name: Real(f"departure_{name}") for name in friends}

    # Initial constraints: start at Union Square at 9:00 AM (9.0)
    current_time = 9.0
    current_location = "Union Square"

    # For each friend, add constraints if they are met
    for name in friends:
        friend = friends[name]
        loc = friend["location"]
        start = friend["start"]
        end = friend["end"]
        min_duration = friend["min_duration"]

        # If meeting this friend, enforce time constraints
        opt.add(Implies(meet[name], arrival[name] >= start))
        opt.add(Implies(meet[name], arrival[name] <= end - min_duration))
        opt.add(Implies(meet[name], departure[name] == arrival[name] + min_duration))

        # Travel time from current location to friend's location
        travel_time = travel_times[(current_location, loc)]
        opt.add(Implies(meet[name], arrival[name] >= current_time + travel_time))

        # Update current_time and current_location if meeting this friend
        current_time = If(meet[name], departure[name], current_time)
        current_location = If(meet[name], loc, current_location)

    # Constraint: meet exactly 7 people
    opt.add(Sum([If(meet[name], 1, 0) for name in friends]) == 7)

    # Objective: maximize total meeting time
    total_meeting_time = Sum([If(meet[name], friends[name]["min_duration"], 0) for name in friends])
    opt.maximize(total_meeting_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        met_friends = [name for name in friends if is_true(m[meet[name]])]
        for name in met_friends:
            print(f"{name}: Arrive at {m[arrival[name]]}, Depart at {m[departure[name]]}")
        print(f"\nTotal meeting time: {sum(friends[name]['min_duration'] for name in met_friends)} hours")
    else:
        print("No solution found.")

solve_scheduling()
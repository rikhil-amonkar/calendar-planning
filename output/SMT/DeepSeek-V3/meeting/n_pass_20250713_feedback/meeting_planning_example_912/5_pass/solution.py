from z3 import *
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Locations and friends data
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
        ("Presidio", "Alamo Square"): 19/60,
        ("Presidio", "Marina District"): 11/60,
        ("Presidio", "Financial District"): 23/60,
        ("Presidio", "Nob Hill"): 18/60,
        ("Presidio", "Sunset District"): 15/60,
        ("Presidio", "Chinatown"): 21/60,
        ("Presidio", "Russian Hill"): 14/60,
        ("Presidio", "North Beach"): 18/60,
        ("Presidio", "Haight-Ashbury"): 15/60,
        ("Alamo Square", "Marina District"): 15/60,
        ("Alamo Square", "Financial District"): 17/60,
        ("Alamo Square", "Nob Hill"): 11/60,
        ("Alamo Square", "Sunset District"): 16/60,
        ("Alamo Square", "Chinatown"): 15/60,
        ("Alamo Square", "Russian Hill"): 13/60,
        ("Alamo Square", "North Beach"): 15/60,
        ("Alamo Square", "Haight-Ashbury"): 5/60,
        ("Marina District", "Financial District"): 17/60,
        ("Marina District", "Nob Hill"): 12/60,
        ("Marina District", "Sunset District"): 19/60,
        ("Marina District", "Chinatown"): 15/60,
        ("Marina District", "Russian Hill"): 8/60,
        ("Marina District", "North Beach"): 11/60,
        ("Marina District", "Haight-Ashbury"): 16/60,
        ("Financial District", "Nob Hill"): 8/60,
        ("Financial District", "Sunset District"): 30/60,
        ("Financial District", "Chinatown"): 5/60,
        ("Financial District", "Russian Hill"): 11/60,
        ("Financial District", "North Beach"): 7/60,
        ("Financial District", "Haight-Ashbury"): 19/60,
        ("Nob Hill", "Sunset District"): 24/60,
        ("Nob Hill", "Chinatown"): 6/60,
        ("Nob Hill", "Russian Hill"): 5/60,
        ("Nob Hill", "North Beach"): 8/60,
        ("Nob Hill", "Haight-Ashbury"): 13/60,
        ("Sunset District", "Chinatown"): 30/60,
        ("Sunset District", "Russian Hill"): 24/60,
        ("Sunset District", "North Beach"): 28/60,
        ("Sunset District", "Haight-Ashbury"): 15/60,
        ("Chinatown", "Russian Hill"): 7/60,
        ("Chinatown", "North Beach"): 3/60,
        ("Chinatown", "Haight-Ashbury"): 19/60,
        ("Russian Hill", "North Beach"): 5/60,
        ("Russian Hill", "Haight-Ashbury"): 17/60,
        ("North Beach", "Haight-Ashbury"): 18/60
    }

    # Select 7 friends to meet
    selected_friends = list(combinations(friends.keys(), 7))[0]  # Just try first combination for demo
    
    # Create variables for arrival and departure times
    arrival = {name: Real(f"arrival_{name}") for name in selected_friends}
    departure = {name: Real(f"departure_{name}") for name in selected_friends}
    
    # Initial constraints
    current_time = 9.0  # Start at Union Square at 9:00 AM
    current_location = "Union Square"
    
    # For each selected friend
    for name in selected_friends:
        friend = friends[name]
        loc = friend["location"]
        start = friend["start"]
        end = friend["end"]
        min_duration = friend["min_duration"]
        
        # Time window constraints
        s.add(arrival[name] >= start)
        s.add(arrival[name] <= end - min_duration)
        s.add(departure[name] == arrival[name] + min_duration)
        
        # Travel time constraint
        travel_time = travel_times.get((current_location, loc), 24/60)  # Default to high if no direct route
        s.add(arrival[name] >= current_time + travel_time)
        
        # Update current time and location
        current_time = departure[name]
        current_location = loc
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in selected_friends:
            print(f"{name}: Arrive at {m[arrival[name]]}, Depart at {m[departure[name]]}")
    else:
        print("No solution found with these 7 friends, trying another combination...")

solve_scheduling()
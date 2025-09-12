from z3 import *
import json

# Define friends data
friends = [
    {
        "name": "Mary",
        "location": "Embarcadero",
        "available_start": 20 * 60,
        "available_end": 21 * 60 + 15,
        "min_duration": 75
    },
    {
        "name": "Kenneth",
        "location": "The Castro",
        "available_start": 11 * 60 + 15,
        "available_end": 19 * 60,
        "min_duration": 30
    },
    {
        "name": "Joseph",
        "location": "Haight-Ashbury",
        "available_start": 20 * 60,
        "available_end": 22 * 60,
        "min_duration": 120
    },
    {
        "name": "Sarah",
        "location": "Union Square",
        "available_start": 11 * 60 + 45,
        "available_end": 14 * 60 + 30,
        "min_duration": 90
    },
    {
        "name": "Thomas",
        "location": "North Beach",
        "available_start": 19 * 60 + 15,
        "available_end": 19 * 60 + 45,
        "min_duration": 15
    },
    {
        "name": "Daniel",
        "location": "Pacific Heights",
        "available_start": 13 * 60 + 45,
        "available_end": 20 * 60 + 30,
        "min_duration": 15
    },
    {
        "name": "Richard",
        "location": "Chinatown",
        "available_start": 8 * 60,
        "available_end": 18 * 60 + 45,
        "min_duration": 30
    },
    {
        "name": "Mark",
        "location": "Golden Gate Park",
        "available_start": 17 * 60 + 30,
        "available_end": 21 * 60 + 30,
        "min_duration": 120
    },
    {
        "name": "David",
        "location": "Marina District",
        "available_start": 20 * 60,
        "available_end": 21 * 60,
        "min_duration": 60
    },
    {
        "name": "Karen",
        "location": "Russian Hill",
        "available_start": 13 * 60 + 15,
        "available_end": 18 * 60 + 30,
        "min_duration": 120
    }
]

# Define travel times
travel_times = {
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
}

# Precompute nob_to_friend and travel_time_matrix
nob_to_friend = [travel_times[("Nob Hill", f["location"])] for f in friends]

travel_time_matrix = []
for i in range(len(friends)):
    row = []
    for j in range(len(friends)):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        row.append(travel_times[(loc_i, loc_j)])
    travel_time_matrix.append(row)

# Create Z3 functions for friend data
available_start_z3 = Function('available_start_z3', IntSort(), IntSort())
available_end_z3 = Function('available_end_z3', IntSort(), IntSort())
min_duration_z3 = Function('min_duration_z3', IntSort(), IntSort())

# Create Z3 functions for travel times
nob_to_friend_z3 = Function('nob_to_friend_z3', IntSort(), IntSort())
travel_time_matrix_z3 = Function('travel_time_matrix_z3', IntSort(), IntSort(), IntSort())

# Solver to add constraints for the functions
solver = Solver()

# Add constraints for friend data functions
for i in range(len(friends)):
    solver.add(available_start_z3(i) == friends[i]["available_start"])
    solver.add(available_end_z3(i) == friends[i]["available_end"])
    solver.add(min_duration_z3(i) == friends[i]["min_duration"])

# Add constraints for travel time functions
for i in range(len(friends)):
    solver.add(nob_to_friend_z3(i) == nob_to_friend[i])
    for j in range(len(friends)):
        solver.add(travel_time_matrix_z3(i, j) == travel_time_matrix[i][j])

# Try to find the maximum number of friends to meet
for K in range(10, 0, -1):
    # Create new solver for each K
    solver_k = Solver()
    # Add the previously defined function constraints
    solver_k.add(solver.assertions())
    
    # Create variables for this K
    friend = [Int(f"friend_{i}") for i in range(K)]
    start = [Int(f"start_{i}") for i in range(K)]
    end_ = [Int(f"end_{i}") for i in range(K)]

    # Constraints for friends to be in 0..9 and unique
    for i in range(K):
        solver_k.add(And(friend[i] >= 0, friend[i] < len(friends)))

    # All friends are unique
    for i in range(K):
        for j in range(i+1, K):
            solver_k.add(friend[i] != friend[j])

    # Constraints for each step
    for i in range(K):
        # start_i >= available_start of friend
        solver_k.add(start[i] >= available_start_z3(friend[i]))
        # end_i = start_i + duration
        solver_k.add(end_[i] == start[i] + min_duration_z3(friend[i]))
        # end_i <= available_end
        solver_k.add(end_[i] <= available_end_z3(friend[i]))

        # Travel time constraint
        if i == 0:
            # Previous location is Nob Hill, current is friend[i]
            solver_k.add(start[i] >= 540 + nob_to_friend_z3(friend[i]))
        else:
            # Previous location is friend[i-1], current is friend[i]
            prev_friend = friend[i-1]
            curr_friend = friend[i]
            solver_k.add(start[i] >= end_[i-1] + travel_time_matrix_z3(prev_friend, curr_friend))

    # Check if the constraints are satisfiable
    if solver_k.check() == sat:
        model = solver_k.model()
        # Extract the solution
        itinerary = []
        for i in range(K):
            friend_idx = model[friend[i]].as_long()
            start_time = model[start[i]].as_long()
            end_time = model[end_[i]].as_long()
            name = friends[friend_idx]["name"]
            location = friends[friend_idx]["location"]
            # Convert start and end times to H:MM format
            def to_time_str(m):
                hours = m // 60
                minutes = m % 60
                return f"{hours}:{minutes:02d}"
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
        # Output the JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
        exit()
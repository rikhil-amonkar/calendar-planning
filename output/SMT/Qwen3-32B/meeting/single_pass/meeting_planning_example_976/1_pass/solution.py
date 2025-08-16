from z3 import *

# Define friends
friends = [
    {
        "name": "Stephanie",
        "location": "Presidio",
        "available_start": 450,  # 7:30 AM
        "available_end": 615,    # 10:15 AM
        "required_duration": 60
    },
    {
        "name": "Brian",
        "location": "Marina District",
        "available_start": 735,  # 12:15 PM
        "available_end": 1800,   # 6:00 PM
        "required_duration": 60
    },
    {
        "name": "Nancy",
        "location": "North Beach",
        "available_start": 885,  # 2:45 PM
        "available_end": 1200,   # 8:00 PM
        "required_duration": 15
    },
    {
        "name": "Thomas",
        "location": "Fisherman's Wharf",
        "available_start": 810,  # 1:30 PM
        "available_end": 1140,   # 7:00 PM
        "required_duration": 30
    },
    {
        "name": "Jessica",
        "location": "Nob Hill",
        "available_start": 930,  # 4:30 PM
        "available_end": 1065,   # 6:45 PM
        "required_duration": 120
    },
    {
        "name": "Mary",
        "location": "Union Square",
        "available_start": 945,  # 4:45 PM
        "available_end": 1290,   # 9:30 PM
        "required_duration": 60
    },
    {
        "name": "Charles",
        "location": "The Castro",
        "available_start": 930,  # 4:30 PM
        "available_end": 1320,   # 10:00 PM
        "required_duration": 105
    },
    {
        "name": "Sarah",
        "location": "Alamo Square",
        "available_start": 1200, # 8:00 PM
        "available_end": 1245,   # 9:45 PM
        "required_duration": 105
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "available_start": 1155, # 7:15 PM
        "available_end": 1275,   # 9:15 PM
        "required_duration": 90
    },
    {
        "name": "Matthew",
        "location": "Bayview",
        "available_start": 1155, # 7:15 PM
        "available_end": 2200,   # 10:00 PM
        "required_duration": 120
    }
]

# Travel times between locations
travel_time = {
    # (from, to): minutes
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10,
}

# Create travel_time_matrix: travel_time_matrix[i][j] is travel time from friend i's location to friend j's location
friend_locations = [f["location"] for f in friends]
travel_time_matrix = [[0 for _ in range(10)] for _ in range(10)]
for i in range(10):
    for j in range(10):
        from_loc = friend_locations[i]
        to_loc = friend_locations[j]
        travel_time_matrix[i][j] = travel_time[(from_loc, to_loc)]

# Z3 solver
s = Optimize()

max_steps = 10

# Variables for each step
friend = [Int(f"friend_{i}") for i in range(max_steps)]
used = [Bool(f"used_{i}") for i in range(max_steps)]
start = [Int(f"start_{i}") for i in range(max_steps)]
end = [Int(f"end_{i}") for i in range(max_steps)]

# Constraints for used and friend variables
for i in range(max_steps):
    s.add(Implies(used[i], And(friend[i] >= 0, friend[i] < 10)))

# For each step, if used, then start and end are defined
for i in range(max_steps):
    # Define available_start, available_end, and required_duration based on friend[i]
    for f_idx in range(10):
        f = friends[f_idx]
        s.add(Implies(And(used[i], friend[i] == f_idx), start[i] >= f["available_start"]))
        s.add(Implies(And(used[i], friend[i] == f_idx), end[i] == start[i] + f["required_duration"]))
        s.add(Implies(And(used[i], friend[i] == f_idx), end[i] <= f["available_end"]))
    
    # Add constraints for arrival time
    if i == 0:
        # First step: arrival time is 540 + travel_time from Embarcadero to friend's location
        for f_idx in range(10):
            from_loc = "Embarcadero"
            to_loc = friend_locations[f_idx]
            travel_time_val = travel_time[(from_loc, to_loc)]
            s.add(Implies(And(used[i], friend[i] == f_idx), start[i] >= 540 + travel_time_val))
    else:
        # For other steps, arrival time is end[i-1] + travel_time from previous friend's location to current friend's location
        for prev_f_idx in range(10):
            for curr_f_idx in range(10):
                travel_time_val = travel_time_matrix[prev_f_idx][curr_f_idx]
                s.add(Implies(
                    And(used[i], used[i-1], friend[i-1] == prev_f_idx, friend[i] == curr_f_idx),
                    start[i] >= end[i-1] + travel_time_val
                ))

# Maximize the number of friends met
num_friends = Sum([If(used[i], 1, 0) for i in range(max_steps)])
s.maximize(num_friends)

# Solve
if s.check() == sat:
    m = s.model()
    # Extract the itinerary
    itinerary = []
    for i in range(max_steps):
        if m.eval(used[i]):
            f_idx = m.eval(friend[i]).as_long()
            start_time = m.eval(start[i]).as_long()
            end_time = m.eval(end[i]).as_long()
            name = friends[f_idx]["name"]
            # Convert start_time and end_time to HH:MM
            def to_time(t):
                h = t // 60
                m = t % 60
                return f"{h:02d}:{m:02d}"
            start_str = to_time(start_time)
            end_str = to_time(end_time)
            itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
    print({"itinerary": itinerary})
else:
    print("No solution found.")
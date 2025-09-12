import z3
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends_data = [
    {
        'name': 'Sandra',
        'availability_start': 600,  # 10:00 AM
        'availability_end': 750,    # 12:30 PM
        'min_duration': 15
    },
    {
        'name': 'William',
        'availability_start': 645,  # 10:45 AM
        'availability_end': 1050,   # 5:30 PM
        'min_duration': 45
    },
    {
        'name': 'Elizabeth',
        'availability_start': 735,  # 12:15 PM
        'availability_end': 900,    # 3:00 PM
        'min_duration': 105
    },
    {
        'name': 'Joseph',
        'availability_start': 765,  # 12:45 PM
        'availability_end': 840,    # 2:00 PM
        'min_duration': 75
    },
    {
        'name': 'Carol',
        'availability_start': 705,  # 11:45 AM
        'availability_end': 975,    # 4:15 PM
        'min_duration': 60
    },
    {
        'name': 'Anthony',
        'availability_start': 780,  # 1:00 PM
        'availability_end': 1230,   # 8:30 PM
        'min_duration': 75
    },
    {
        'name': 'Barbara',
        'availability_start': 1155, # 7:15 PM
        'availability_end': 1230,   # 8:30 PM
        'min_duration': 75
    },
    {
        'name': 'Stephanie',
        'availability_start': 975,  # 4:15 PM
        'availability_end': 1290,   # 9:30 PM
        'min_duration': 75
    },
    {
        'name': 'Kenneth',
        'availability_start': 1275, # 9:15 PM
        'availability_end': 1335,   # 10:15 PM
        'min_duration': 45
    },
]

friends_locations = [8, 2, 3, 4, 7, 5, 6, 1, 9]  # for friend indices 0-8

travel_time = [
    # Marina to each district
    [0, 11, 16, 12, 10, 18, 14, 17, 11, 10],
    # Richmond
    [9, 0, 21, 17, 18, 9, 19, 22, 17, 7],
    # Union Square
    [18, 20, 0, 9, 15, 22, 11, 9, 10, 24],
    # Nob Hill
    [11, 14, 7, 0, 10, 17, 9, 9, 8, 17],
    # Fisherman's Wharf
    [9, 18, 13, 11, 0, 25, 8, 11, 6, 17],
    # Golden Gate Park
    [16, 7, 22, 20, 24, 0, 25, 26, 23, 11],
    # Embarcadero
    [12, 21, 10, 10, 6, 25, 0, 5, 5, 20],
    # Financial District
    [15, 21, 9, 8, 10, 23, 4, 0, 7, 22],
    # North Beach
    [9, 18, 7, 7, 5, 22, 6, 8, 0, 17],
    # Presidio
    [11, 7, 22, 18, 19, 12, 20, 23, 18, 0]
]

districts = [
    "Marina District",
    "Richmond District",
    "Union Square",
    "Nob Hill",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Embarcadero",
    "Financial District",
    "North Beach",
    "Presidio"
]

solver = z3.Optimize()

NUM_STEPS = 10  # 0 to 9

used = []
friend = []
start = []
end = []

for i in range(NUM_STEPS):
    used_i = z3.Bool(f"used_{i}")
    friend_i = z3.Int(f"friend_{i}")
    start_i = z3.Int(f"start_{i}")
    end_i = z3.Int(f"end_{i}")
    used.append(used_i)
    friend.append(friend_i)
    start.append(start_i)
    end.append(end_i)

# Constraints for each step
for i in range(NUM_STEPS):
    # Ensure friend[i] is a valid index
    solver.add(z3.Implies(used[i], friend[i] >= 0))
    solver.add(z3.Implies(used[i], friend[i] <= 8))

    # Availability constraints for each possible friend
    for j in range(len(friends_data)):
        solver.add(z3.Implies(z3.And(used[i], friend[i] == j), start[i] >= friends_data[j]['availability_start']))
        solver.add(z3.Implies(z3.And(used[i], friend[i] == j), end[i] <= friends_data[j]['availability_end']))
        solver.add(z3.Implies(z3.And(used[i], friend[i] == j), end[i] - start[i] >= friends_data[j]['min_duration']))

    # Initial time constraint for step 0
    if i == 0:
        for j in range(len(friends_data)):
            loc = friends_locations[j]
            travel_time_val = travel_time[0][loc]
            solver.add(z3.Implies(z3.And(used[i], friend[i] == j), start[i] >= 540 + travel_time_val))

# Constraints between steps i and j (i < j)
for i in range(NUM_STEPS):
    for j in range(i + 1, NUM_STEPS):
        for friend_a in range(len(friends_data)):
            for friend_b in range(len(friends_data)):
                loc_i = friends_locations[friend_a]
                loc_j = friends_locations[friend_b]
                travel_time_val = travel_time[loc_i][loc_j]
                solver.add(z3.Implies(
                    z3.And(used[i], used[j], friend[i] == friend_a, friend[j] == friend_b),
                    start[j] >= end[i] + travel_time_val
                ))

# Ensure each friend is used at most once
for j in range(len(friends_data)):
    constraints = []
    for i in range(NUM_STEPS):
        constraints.append(z3.If(z3.And(used[i], friend[i] == j), 1, 0))
    total = z3.Sum(constraints)
    solver.add(total <= 1)

# Maximize the number of used steps
objective = z3.Sum([z3.If(used[i], 1, 0) for i in range(NUM_STEPS)])
solver.maximize(objective)

# Solve
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(NUM_STEPS):
        if model.evaluate(used[i], model_completion=True):
            friend_idx = model.evaluate(friend[i], model_completion=True).as_long()
            start_time = model.evaluate(start[i], model_completion=True).as_long()
            end_time = model.evaluate(end[i], model_completion=True).as_long()
            loc_idx = friends_locations[friend_idx]
            district_name = districts[loc_idx]
            friend_name = friends_data[friend_idx]['name']
            itinerary.append({
                "action": "meet",
                "location": district_name,
                "person": friend_name,
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")
import z3

# Define friends and their details
friends = [
    {
        'name': 'Jessica',
        'location': 'Russian Hill',
        'availability_start': 540,  # 9:00 AM
        'availability_end': 900,    # 3:00 PM
        'required_duration': 120,
    },
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'availability_start': 585,  # 9:45 AM
        'availability_end': 780,    # 1:00 PM
        'required_duration': 45,
    },
    {
        'name': 'Rebecca',
        'location': 'Sunset District',
        'availability_start': 525,  # 8:45 AM
        'availability_end': 900,    # 3:00 PM
        'required_duration': 75,
    },
    {
        'name': 'John',
        'location': 'North Beach',
        'availability_start': 585,  # 9:45 AM
        'availability_end': 1080,   # 6:00 PM
        'required_duration': 15,
    },
    {
        'name': 'Jason',
        'location': 'Marina District',
        'availability_start': 1035, # 3:15 PM
        'availability_end': 1140,   # 9:45 PM
        'required_duration': 120,
    },
    {
        'name': 'Mark',
        'location': 'Fisherman\'s Wharf',
        'availability_start': 1035, # 5:15 PM
        'availability_end': 1200,   # 8:00 PM
        'required_duration': 90,
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'availability_start': 1245, # 8:45 PM
        'availability_end': 1305,   # 9:45 PM
        'required_duration': 60,
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'availability_start': 1005, # 4:45 PM
        'availability_end': 1140,   # 7:00 PM
        'required_duration': 75,
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'availability_start': 1050, # 5:30 PM
        'availability_end': 1095,   # 6:15 PM
        'required_duration': 45,
    },
    {
        'name': 'Amanda',
        'location': 'The Castro',
        'availability_start': 1200, # 8:00 PM
        'availability_end': 1275,   # 9:15 PM
        'required_duration': 60,
    },
]

# Define travel times between locations
locations = ['Union Square', 'Mission District', 'Fisherman\'s Wharf', 'Russian Hill', 'Marina District', 'North Beach', 'Chinatown', 'Pacific Heights', 'The Castro', 'Nob Hill', 'Sunset District']

travel_time = {
    'Union Square': {
        'Mission District': 14,
        'Fisherman\'s Wharf': 15,
        'Russian Hill': 13,
        'Marina District': 18,
        'North Beach': 10,
        'Chinatown': 7,
        'Pacific Heights': 15,
        'The Castro': 17,
        'Nob Hill': 9,
        'Sunset District': 27,
    },
    'Mission District': {
        'Union Square': 15,
        'Fisherman\'s Wharf': 22,
        'Russian Hill': 15,
        'Marina District': 19,
        'North Beach': 17,
        'Chinatown': 16,
        'Pacific Heights': 16,
        'The Castro': 7,
        'Nob Hill': 12,
        'Sunset District': 24,
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'Mission District': 22,
        'Russian Hill': 7,
        'Marina District': 9,
        'North Beach': 6,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'The Castro': 27,
        'Nob Hill': 11,
        'Sunset District': 27,
    },
    'Russian Hill': {
        'Union Square': 10,
        'Mission District': 16,
        'Fisherman\'s Wharf': 7,
        'Marina District': 7,
        'North Beach': 5,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'The Castro': 21,
        'Nob Hill': 5,
        'Sunset District': 23,
    },
    'Marina District': {
        'Union Square': 16,
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Pacific Heights': 7,
        'The Castro': 22,
        'Nob Hill': 12,
        'Sunset District': 19,
    },
    'North Beach': {
        'Union Square': 7,
        'Mission District': 18,
        'Fisherman\'s Wharf': 5,
        'Russian Hill': 4,
        'Marina District': 9,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 23,
        'Nob Hill': 7,
        'Sunset District': 27,
    },
    'Chinatown': {
        'Union Square': 7,
        'Mission District': 17,
        'Fisherman\'s Wharf': 8,
        'Russian Hill': 7,
        'Marina District': 12,
        'North Beach': 3,
        'Pacific Heights': 10,
        'The Castro': 22,
        'Nob Hill': 9,
        'Sunset District': 29,
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Mission District': 15,
        'Fisherman\'s Wharf': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'North Beach': 9,
        'Chinatown': 11,
        'The Castro': 16,
        'Nob Hill': 8,
        'Sunset District': 21,
    },
    'The Castro': {
        'Union Square': 19,
        'Mission District': 7,
        'Fisherman\'s Wharf': 24,
        'Russian Hill': 18,
        'Marina District': 21,
        'North Beach': 20,
        'Chinatown': 22,
        'Pacific Heights': 16,
        'Nob Hill': 16,
        'Sunset District': 17,
    },
    'Nob Hill': {
        'Union Square': 7,
        'Mission District': 13,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 5,
        'Marina District': 11,
        'North Beach': 8,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 17,
        'Sunset District': 24,
    },
    'Sunset District': {
        'Union Square': 30,
        'Mission District': 25,
        'Fisherman\'s Wharf': 29,
        'Russian Hill': 24,
        'Marina District': 21,
        'North Beach': 28,
        'Chinatown': 30,
        'Pacific Heights': 21,
        'The Castro': 17,
        'Nob Hill': 27,
    },
}

# Z3 solver setup
solver = z3.Optimize()

include = [z3.Bool(f"include_{i}") for i in range(len(friends))]
start = [z3.Int(f"start_{i}") for i in range(len(friends))]
end = [z3.Int(f"end_{i}") for i in range(len(friends))]
pos = [z3.Int(f"pos_{i}") for i in range(len(friends))]

# Add constraints for each friend
for i in range(len(friends)):
    # If included, start and end constraints
    solver.add(z3.Implies(include[i], z3.And(
        start[i] >= friends[i]['availability_start'],
        start[i] <= friends[i]['availability_end'],
        end[i] == start[i] + friends[i]['required_duration']
    )))

    # First friend constraint
    cond = include[i]
    for j in range(len(friends)):
        if j != i:
            cond = z3.And(cond, z3.Implies(include[j], pos[j] >= pos[i]))
    arrival_time = 540 + travel_time['Union Square'][friends[i]['location']]
    solver.add(z3.Implies(cond, start[i] >= arrival_time))

# Ensure unique positions for included friends
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        solver.add(z3.Implies(z3.And(include[i], include[j]), pos[i] != pos[j]))

# Add constraints for pairs of friends
for i in range(len(friends)):
    for j in range(len(friends)):
        if i != j:
            loc_i = friends[i]['location']
            loc_j = friends[j]['location']
            tt = travel_time[loc_i][loc_j]
            solver.add(z3.Implies(z3.And(include[i], include[j], pos[i] < pos[j]), start[j] >= end[i] + tt))

# Maximize the number of included friends
objective = z3.Sum([z3.If(include[i], 1, 0) for i in range(len(friends))])
solver.maximize(objective)

# Check solution
result = solver.check()
if result == z3.sat:
    model = solver.model()
    included = []
    for i in range(len(friends)):
        if model.evaluate(include[i]):
            s = model.evaluate(start[i])
            e = model.evaluate(end[i])
            name = friends[i]['name']
            included.append({
                'name': name,
                'start': s,
                'end': e
            })
    # Sort by start time
    included.sort(key=lambda x: x['start'])
    # Convert to HH:MM format
    itinerary = []
    for item in included:
        start_min = item['start']
        end_min = item['end']
        start_h = start_min // 60
        start_m = start_min % 60
        end_h = end_min // 60
        end_m = end_min % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_time = f"{end_h:02d}:{end_m:02d}"
        itinerary.append({
            "action": "meet",
            "person": item['name'],
            "start_time": start_time,
            "end_time": end_time
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")
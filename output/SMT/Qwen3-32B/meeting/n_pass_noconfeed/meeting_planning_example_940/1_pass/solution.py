from z3 import *
import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends_data = [
    {
        'name': 'Jessica',
        'location': 'Russian Hill',
        'available_start': 9 * 60,
        'available_end': 15 * 60,
        'duration': 120,
    },
    {
        'name': 'Rebecca',
        'location': 'Sunset District',
        'available_start': 8 * 60 + 45,
        'available_end': 15 * 60,
        'duration': 75,
    },
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'available_start': 9 * 60 + 45,
        'available_end': 13 * 60,
        'duration': 45,
    },
    {
        'name': 'John',
        'location': 'North Beach',
        'available_start': 9 * 60 + 45,
        'available_end': 18 * 60,
        'duration': 15,
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'available_start': 16 * 60 + 45,
        'available_end': 19 * 60,
        'duration': 75,
    },
    {
        'name': 'Jason',
        'location': 'Marina District',
        'available_start': 15 * 60 + 15,
        'available_end': 21 * 60 + 45,
        'duration': 120,
    },
    {
        'name': 'Mark',
        'location': 'Fisherman\'s Wharf',
        'available_start': 17 * 60 + 15,
        'available_end': 20 * 60,
        'duration': 90,
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'available_start': 17 * 60 + 30,
        'available_end': 18 * 60 + 15,
        'duration': 45,
    },
    {
        'name': 'Amanda',
        'location': 'The Castro',
        'available_start': 20 * 60,
        'available_end': 21 * 60 + 15,
        'duration': 60,
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'available_start': 20 * 60 + 45,
        'available_end': 21 * 60 + 45,
        'duration': 60,
    },
]

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

friends = friends_data
n = len(friends)

solver = Optimize()

include = [Bool(f"include_{i}") for i in range(n)]
S = [Int(f"S_{i}") for i in range(n)]
E = [Int(f"E_{i}") for i in range(n)]

# For each friend, if included, E_i = S_i + duration_i
for i in range(n):
    solver.add(Implies(include[i], E[i] == S[i] + friends[i]['duration']))

# For each friend, if included, S_i is within available window
for i in range(n):
    solver.add(Implies(include[i], And(S[i] >= friends[i]['available_start'], S[i] + friends[i]['duration'] <= friends[i]['available_end'])))

# Order constraints between pairs of friends
order = [[Bool(f"order_{i}_{j}") for j in range(n)] for i in range(n)]

for i in range(n):
    for j in range(n):
        if i == j:
            continue
        # If both include_i and include_j, then order_ij and order_ji cannot both be true
        solver.add(Implies(And(include[i], include[j]), Not(And(order[i][j], order[j][i]))))

        # If order_ij is true, then S_j >= E_i + travel_time from i's loc to j's loc
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        travel = travel_time[loc_i][loc_j]
        solver.add(Implies(And(include[i], include[j], order[i][j]), S[j] >= E[i] + travel))

        # Similarly for order_ji
        travel_back = travel_time[loc_j][loc_i]
        solver.add(Implies(And(include[i], include[j], order[j][i]), S[i] >= E[j] + travel_back))

# First meeting constraint
for i in range(n):
    # For each friend i, if include[i] is true and no other friend j has order[j][i] true, then S_i >= 540 + travel from Union Square to i's loc
    constraints = []
    for j in range(n):
        if j != i:
            constraints.append(Not(order[j][i]))
    no_previous = And(constraints)
    loc_i = friends[i]['location']
    travel_from_union = travel_time['Union Square'][loc_i]
    solver.add(Implies(And(include[i], no_previous), S[i] >= 540 + travel_from_union))

# Maximize the number of included friends
solver.maximize(Sum([If(include[i], 1, 0) for i in range(n)]))

# Solve
if solver.check() == sat:
    model = solver.model()
    included = []
    for i in range(n):
        if is_true(model.evaluate(include[i])):
            included.append(i)
    # Extract start times and sort by start time
    schedule = []
    for i in included:
        start = model.evaluate(S[i]).as_long()
        end = start + friends[i]['duration']
        schedule.append({
            'person': friends[i]['name'],
            'location': friends[i]['location'],
            'start_time': time_to_str(start),
            'end_time': time_to_str(end)
        })
    # Sort by start time
    schedule.sort(key=lambda x: x['start_time'])
    # Create itinerary
    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item['location'],
            "person": item['person'],
            "start_time": item['start_time'],
            "end_time": item['end_time']
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")
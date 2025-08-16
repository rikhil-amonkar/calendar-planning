import z3
import json
from collections import defaultdict, deque

friends = [
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'available_start': 0,
        'available_end': 240,
        'min_duration': 45
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'available_start': 0,
        'available_end': 390,
        'min_duration': 15
    },
    {
        'name': 'Lisa',
        'location': 'Financial District',
        'available_start': 105,
        'available_end': 495,
        'min_duration': 15
    },
    {
        'name': 'Melissa',
        'location': 'Russian Hill',
        'available_start': 480,
        'available_end': 765,
        'min_duration': 120
    },
    {
        'name': 'Sarah',
        'location': 'Richmond District',
        'available_start': 435,
        'available_end': 630,
        'min_duration': 105
    },
    {
        'name': 'Stephanie',
        'location': "Fisherman's Wharf",
        'available_start': 390,
        'available_end': 780,
        'min_duration': 30
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': 645,
        'available_end': 780,
        'min_duration': 105
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'available_start': 105,
        'available_end': 315,
        'min_duration': 60
    },
    {
        'name': 'Daniel',
        'location': 'Pacific Heights',
        'available_start': 570,
        'available_end': 765,
        'min_duration': 60
    },
    {
        'name': 'John',
        'location': 'The Castro',
        'available_start': 255,
        'available_end': 645,
        'min_duration': 45
    }
]

num_friends = len(friends)

travel_time = {
    'Embarcadero': {
        "Fisherman's Wharf": 6,
        'Financial District': 5,
        'Russian Hill': 8,
        'Marina District': 12,
        'Richmond District': 21,
        'Pacific Heights': 11,
        'Haight-Ashbury': 21,
        'Presidio': 20,
        'Nob Hill': 10,
        'The Castro': 25
    },
    "Fisherman's Wharf": {
        'Embarcadero': 8,
        'Financial District': 11,
        'Russian Hill': 7,
        'Marina District': 9,
        'Richmond District': 18,
        'Pacific Heights': 12,
        'Haight-Ashbury': 22,
        'Presidio': 17,
        'Nob Hill': 11,
        'The Castro': 27
    },
    'Financial District': {
        'Embarcadero': 4,
        "Fisherman's Wharf": 10,
        'Russian Hill': 11,
        'Marina District': 15,
        'Richmond District': 21,
        'Pacific Heights': 13,
        'Haight-Ashbury': 19,
        'Presidio': 22,
        'Nob Hill': 8,
        'The Castro': 20
    },
    'Russian Hill': {
        'Embarcadero': 8,
        "Fisherman's Wharf": 7,
        'Financial District': 11,
        'Marina District': 7,
        'Richmond District': 14,
        'Pacific Heights': 7,
        'Haight-Ashbury': 17,
        'Presidio': 14,
        'Nob Hill': 5,
        'The Castro': 21
    },
    'Marina District': {
        'Embarcadero': 14,
        "Fisherman's Wharf": 10,
        'Financial District': 17,
        'Russian Hill': 8,
        'Richmond District': 11,
        'Pacific Heights': 7,
        'Haight-Ashbury': 16,
        'Presidio': 10,
        'Nob Hill': 12,
        'The Castro': 22
    },
    'Richmond District': {
        'Embarcadero': 19,
        "Fisherman's Wharf": 18,
        'Financial District': 22,
        'Russian Hill': 13,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Haight-Ashbury': 10,
        'Presidio': 7,
        'Nob Hill': 17,
        'The Castro': 16
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        "Fisherman's Wharf": 13,
        'Financial District': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'Richmond District': 12,
        'Haight-Ashbury': 11,
        'Presidio': 11,
        'Nob Hill': 8,
        'The Castro': 16
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        "Fisherman's Wharf": 23,
        'Financial District': 21,
        'Russian Hill': 17,
        'Marina District': 17,
        'Richmond District': 10,
        'Pacific Heights': 12,
        'Presidio': 15,
        'Nob Hill': 15,
        'The Castro': 6
    },
    'Presidio': {
        'Embarcadero': 20,
        "Fisherman's Wharf": 19,
        'Financial District': 23,
        'Russian Hill': 14,
        'Marina District': 11,
        'Richmond District': 7,
        'Pacific Heights': 11,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'The Castro': 21
    },
    'Nob Hill': {
        'Embarcadero': 9,
        "Fisherman's Wharf": 10,
        'Financial District': 9,
        'Russian Hill': 5,
        'Marina District': 11,
        'Richmond District': 14,
        'Pacific Heights': 8,
        'Haight-Ashbury': 13,
        'Presidio': 17,
        'The Castro': 17
    },
    'The Castro': {
        'Embarcadero': 22,
        "Fisherman's Wharf": 24,
        'Financial District': 21,
        'Russian Hill': 18,
        'Marina District': 21,
        'Richmond District': 16,
        'Pacific Heights': 16,
        'Haight-Ashbury': 6,
        'Presidio': 20,
        'Nob Hill': 16
    }
}

opt = z3.Optimize()

include = []
start = []
end = []
before = [[None for _ in range(num_friends)] for _ in range(num_friends)]

for i in range(num_friends):
    include_i = z3.Bool('include_{}'.format(i))
    include.append(include_i)
    start_i = z3.Int('start_{}'.format(i))
    start.append(start_i)
    end_i = z3.Int('end_{}'.format(i))
    end.append(end_i)
    for j in range(num_friends):
        if i != j:
            before[i][j] = z3.Bool('before_{}_{}'.format(i, j))

for i in range(num_friends):
    opt.add(z3.Implies(include[i], end[i] == start[i] + friends[i]['min_duration']))
    opt.add(z3.Implies(include[i], start[i] >= friends[i]['available_start']))
    opt.add(z3.Implies(include[i], end[i] <= friends[i]['available_end']))
    loc_i = friends[i]['location']
    travel_time_emb_to_i = travel_time['Embarcadero'][loc_i]
    opt.add(z3.Implies(include[i], start[i] >= travel_time_emb_to_i))

for i in range(num_friends):
    for j in range(num_friends):
        if i != j:
            opt.add(z3.Implies(z3.And(include[i], include[j]), z3.Xor(before[i][j], before[j][i])))

for i in range(num_friends):
    for j in range(num_friends):
        if i != j:
            loc_j = friends[j]['location']
            loc_i = friends[i]['location']
            travel_time_j_to_i = travel_time[loc_j][loc_i]
            opt.add(z3.Implies(before[j][i], start[i] >= end[j] + travel_time_j_to_i))

objective = z3.Sum([z3.If(include[i], 1, 0) for i in range(num_friends)])
opt.maximize(objective)

result = opt.check()
if result == z3.sat:
    model = opt.model()
    included = []
    for i in range(num_friends):
        if model.eval(include[i]):
            included.append(i)
    edges = defaultdict(list)
    for i in included:
        for j in included:
            if i != j and model.eval(before[i][j]):
                edges[i].append(j)
    in_degree = defaultdict(int)
    for u in edges:
        for v in edges[u]:
            in_degree[v] += 1
    queue = deque()
    for node in included:
        if in_degree[node] == 0:
            queue.append(node)
    order = []
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in edges[u]:
            in_degree[v] -= 1
            if in_degree[v] == 0:
                queue.append(v)
    itinerary = []
    for u in order:
        start_time_minutes = model.eval(start[u]).as_long()
        end_time_minutes = model.eval(end[u]).as_long()
        start_time = (9 * 60 + start_time_minutes) // 60
        start_min = (9 * 60 + start_time_minutes) % 60
        end_time = (9 * 60 + end_time_minutes) // 60
        end_min = (9 * 60 + end_time_minutes) % 60
        start_str = f"{start_time:02d}:{start_min:02d}"
        end_str = f"{end_time:02d}:{end_min:02d}"
        itinerary.append({
            "action": "meet",
            "person": friends[u]['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")
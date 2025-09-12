import z3
import json

friends = [
    {
        'name': 'Andrew',
        'location': 'Golden Gate Park',
        'earliest': 705,
        'latest': 870,
        'duration': 75
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'earliest': 975,
        'latest': 1125,
        'duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'earliest': 1050,
        'latest': 1155,
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Chinatown',
        'earliest': 585,
        'latest': 1290,
        'duration': 90
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'earliest': 510,
        'latest': 855,
        'duration': 30
    }
]

travel_time = {
    'Union Square': {
        'Golden Gate Park': 22,
        'Pacific Heights': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'The Castro': 19
    },
    'Golden Gate Park': {
        'Union Square': 22,
        'Pacific Heights': 16,
        'Presidio': 11,
        'Chinatown': 23,
        'The Castro': 13
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Presidio': 11,
        'Chinatown': 11,
        'The Castro': 16
    },
    'Presidio': {
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Pacific Heights': 11,
        'Chinatown': 21,
        'The Castro': 21
    },
    'Chinatown': {
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Pacific Heights': 10,
        'Presidio': 19,
        'The Castro': 22
    },
    'The Castro': {
        'Union Square': 19,
        'Golden Gate Park': 11,
        'Pacific Heights': 16,
        'Presidio': 20,
        'Chinatown': 20
    }
}

meet = []
start = []
end = []
for friend in friends:
    name = friend['name']
    meet.append(z3.Bool(f'meet_{name}'))
    start.append(z3.Int(f'start_{name}'))
    end.append(z3.Int(f'end_{name}'))

opt = z3.Optimize()

for i in range(len(friends)):
    friend = friends[i]
    loc = friend['location']
    earliest = friend['earliest']
    latest = friend['latest']
    duration = friend['duration']
    opt.add(z3.Implies(meet[i], start[i] >= earliest))
    opt.add(z3.Implies(meet[i], end[i] <= latest))
    opt.add(z3.Implies(meet[i], end[i] - start[i] >= duration))
    opt.add(z3.Implies(meet[i], start[i] >= 540 + travel_time['Union Square'][loc]))

for i in range(len(friends)):
    for j in range(len(friends)):
        if i != j:
            loc_i = friends[i]['location']
            loc_j = friends[j]['location']
            travel_time_ij = travel_time[loc_i][loc_j]
            opt.add(z3.Implies(z3.And(meet[i], meet[j]), z3.Or(
                start[j] >= end[i] + travel_time_ij,
                start[i] >= end[j] + travel_time[loc_j][loc_i]
            )))

opt.maximize(z3.Sum([z3.If(m, 1, 0) for m in meet]))

if opt.check() == z3.sat:
    model = opt.model()
    met_friends = []
    for i in range(len(friends)):
        if model.eval(meet[i]):
            met_friends.append({
                'name': friends[i]['name'],
                'location': friends[i]['location'],
                'start': model.eval(start[i]),
                'end': model.eval(end[i])
            })
    met_friends.sort(key=lambda x: x['start'].as_long())
    itinerary = []
    for f in met_friends:
        start_time = f['start'].as_long()
        end_time = f['end'].as_long()
        def to_time_str(t):
            hours = t // 60
            minutes = t % 60
            return f"{hours}:{minutes:02d}"
        itinerary.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))
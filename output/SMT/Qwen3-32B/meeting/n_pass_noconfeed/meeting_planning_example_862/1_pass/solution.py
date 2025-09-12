import z3
import json

friends = [
    {'name': 'Laura', 'location_idx': 1, 'available_start': 870, 'available_end': 975, 'min_duration': 75},
    {'name': 'Brian', 'location_idx': 2, 'available_start': 615, 'available_end': 1140, 'min_duration': 30},
    {'name': 'Karen', 'location_idx': 3, 'available_start': 1080, 'available_end': 1215, 'min_duration': 90},
    {'name': 'Stephanie', 'location_idx': 4, 'available_start': 615, 'available_end': 900, 'min_duration': 75},
    {'name': 'Helen', 'location_idx': 5, 'available_start': 690, 'available_end': 1305, 'min_duration': 120},
    {'name': 'Sandra', 'location_idx': 6, 'available_start': 480, 'available_end': 975, 'min_duration': 30},
    {'name': 'Mary', 'location_idx': 7, 'available_start': 1005, 'available_end': 1125, 'min_duration': 120},
    {'name': 'Deborah', 'location_idx': 8, 'available_start': 1140, 'available_end': 1245, 'min_duration': 105},
    {'name': 'Elizabeth', 'location_idx': 9, 'available_start': 510, 'available_end': 795, 'min_duration': 105},
]

travel_pairs = [
    (0, 1, 11), (0, 2, 25), (0, 3, 15), (0, 4, 17), (0, 5, 17), (0, 6, 20), (0, 7, 19), (0, 8, 15), (0, 9, 19),
    (1, 0, 10), (1, 2, 17), (1, 3, 13), (1, 4, 15), (1, 5, 9), (1, 6, 11), (1, 7, 16), (1, 8, 17), (1, 9, 15),
    (2, 0, 26), (2, 1, 19), (2, 3, 14), (2, 4, 18), (2, 5, 12), (2, 6, 7), (2, 7, 20), (2, 8, 23), (2, 9, 11),
    (3, 0, 16), (3, 1, 15), (3, 2, 14), (3, 4, 5), (3, 5, 21), (3, 6, 14), (3, 7, 8), (3, 8, 11), (3, 9, 7),
    (4, 0, 18), (4, 1, 16), (4, 2, 17), (4, 3, 4), (4, 5, 22), (4, 6, 18), (4, 7, 6), (4, 8, 8), (4, 9, 9),
    (5, 0, 17), (5, 1, 9), (5, 2, 11), (5, 3, 19), (5, 4, 23), (5, 6, 7), (5, 7, 25), (5, 8, 26), (5, 9, 16),
    (6, 0, 20), (6, 1, 13), (6, 2, 7), (6, 3, 13), (6, 4, 17), (6, 5, 9), (6, 7, 19), (6, 8, 22), (6, 9, 9),
    (7, 0, 20), (7, 1, 19), (7, 2, 20), (7, 3, 8), (7, 4, 5), (7, 5, 25), (7, 6, 21), (7, 8, 5), (7, 9, 12),
    (8, 0, 17), (8, 1, 17), (8, 2, 22), (8, 3, 11), (8, 4, 7), (8, 5, 23), (8, 6, 21), (8, 7, 4), (8, 9, 15),
    (9, 0, 20), (9, 1, 15), (9, 2, 10), (9, 3, 8), (9, 4, 11), (9, 5, 18), (9, 6, 11), (9, 7, 14), (9, 8, 17),
]

def get_travel_time_z3(loc_prev, loc_current):
    expr = 0
    for from_loc, to_loc, time in travel_pairs:
        expr = z3.If(z3.And(loc_prev == from_loc, loc_current == to_loc), time, expr)
    return expr

max_steps = 9
is_used = [z3.Bool(f'is_used_{i}') for i in range(max_steps)]
friend_idx = [z3.Int(f'friend_idx_{i}') for i in range(max_steps)]
start = [z3.Int(f'start_{i}') for i in range(max_steps)]
end = [z3.Int(f'end_{i}') for i in range(max_steps)]
location_idx = [z3.Int(f'location_idx_{i}') for i in range(max_steps)]

opt = z3.Optimize()

for i in range(max_steps):
    opt.add(z3.Implies(is_used[i], z3.And(friend_idx[i] >= 0, friend_idx[i] <= 8)))

    for j in range(9):
        opt.add(z3.Implies(z3.And(is_used[i], friend_idx[i] == j), location_idx[i] == friends[j]['location_idx']))

    for j in range(9):
        available_start = friends[j]['available_start']
        available_end = friends[j]['available_end']
        opt.add(z3.Implies(z3.And(is_used[i], friend_idx[i] == j), z3.And(start[i] >= available_start, start[i] <= available_end)))

    for j in range(9):
        min_duration = friends[j]['min_duration']
        available_end = friends[j]['available_end']
        opt.add(z3.Implies(z3.And(is_used[i], friend_idx[i] == j), z3.And(end[i] >= start[i] + min_duration, end[i] <= available_end)))

    if i == 0:
        travel_time_expr = get_travel_time_z3(0, location_idx[i])
        opt.add(z3.Implies(is_used[i], start[i] >= 540 + travel_time_expr))
    else:
        prev_loc = location_idx[i-1]
        curr_loc = location_idx[i]
        travel_time_expr = get_travel_time_z3(prev_loc, curr_loc)
        opt.add(z3.Implies(z3.And(is_used[i], is_used[i-1]), start[i] >= end[i-1] + travel_time_expr))

        travel_time_expr = get_travel_time_z3(0, curr_loc)
        opt.add(z3.Implies(z3.And(is_used[i], z3.Not(is_used[i-1])), start[i] >= 540 + travel_time_expr))

num_meetings = z3.Sum([z3.If(is_used[i], 1, 0) for i in range(max_steps)])
opt.maximize(num_meetings)

result = opt.check()
if result == z3.sat:
    model = opt.model()
    itinerary = []
    locations_list = [
        'Mission District',
        'Alamo Square',
        'Presidio',
        'Russian Hill',
        'North Beach',
        'Golden Gate Park',
        'Richmond District',
        'Embarcadero',
        'Financial District',
        'Marina District'
    ]
    for i in range(max_steps):
        if model.eval(is_used[i]).is_true():
            idx = model.eval(friend_idx[i]).as_long()
            friend = friends[idx]['name']
            loc_idx = model.eval(location_idx[i]).as_long()
            location_name = locations_list[loc_idx]
            start_time = model.eval(start[i]).as_long()
            end_time = model.eval(end[i]).as_long()
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            itinerary.append({
                "action": "meet",
                "location": location_name,
                "person": friend,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")
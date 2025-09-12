from z3 import *
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {'name': 'Helen', 'location': 'North Beach', 'available_start': 660, 'available_end': 735, 'min_duration': 45},
    {'name': 'Mary', 'location': 'Nob Hill', 'available_start': 1050, 'available_end': 1140, 'min_duration': 45},
    {'name': 'Barbara', 'location': 'Alamo Square', 'available_start': 1020, 'available_end': 1140, 'min_duration': 120},
    {'name': 'Mark', 'location': 'Marina District', 'available_start': 1095, 'available_end': 1185, 'min_duration': 75},
    {'name': 'Emily', 'location': 'Fisherman\'s Wharf', 'available_start': 975, 'available_end': 1140, 'min_duration': 30},
    {'name': 'Laura', 'location': 'Sunset District', 'available_start': 1140, 'available_end': 1275, 'min_duration': 75},
    {'name': 'Michelle', 'location': 'Golden Gate Park', 'available_start': 1200, 'available_end': 1260, 'min_duration': 15},
]

travel_times = {
    'Presidio': {
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
        'Alamo Square': 19,
        'Sunset District': 15,
        'Nob Hill': 18,
        'North Beach': 18,
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Alamo Square': 10,
        'Sunset District': 21,
        'Nob Hill': 8,
        'North Beach': 9,
    },
    'Golden Gate Park': {
        'Presidio': 12,
        'Pacific Heights': 15,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Alamo Square': 9,
        'Sunset District': 10,
        'Nob Hill': 20,
        'North Beach': 23,
    },
    'Fisherman\'s Wharf': {
        'Presidio': 19,
        'Pacific Heights': 13,
        'Golden Gate Park': 24,
        'Marina District': 9,
        'Alamo Square': 21,
        'Sunset District': 27,
        'Nob Hill': 11,
        'North Beach': 6,
    },
    'Marina District': {
        'Presidio': 11,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 15,
        'Sunset District': 19,
        'Nob Hill': 12,
        'North Beach': 11,
    },
    'Alamo Square': {
        'Presidio': 19,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Fisherman\'s Wharf': 21,
        'Marina District': 15,
        'Sunset District': 16,
        'Nob Hill': 11,
        'North Beach': 15,
    },
    'Sunset District': {
        'Presidio': 15,
        'Pacific Heights': 21,
        'Golden Gate Park': 10,
        'Fisherman\'s Wharf': 27,
        'Marina District': 19,
        'Alamo Square': 16,
        'Nob Hill': 27,
        'North Beach': 28,
    },
    'Nob Hill': {
        'Presidio': 18,
        'Pacific Heights': 8,
        'Golden Gate Park': 20,
        'Fisherman\'s Wharf': 10,
        'Marina District': 12,
        'Alamo Square': 11,
        'Sunset District': 27,
        'North Beach': 8,
    },
    'North Beach': {
        'Presidio': 18,
        'Pacific Heights': 9,
        'Golden Gate Park': 23,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
        'Alamo Square': 16,
        'Sunset District': 28,
        'Nob Hill': 7,
    },
}

num_steps = 7
s = Solver()

friend_idx = [Int(f'friend_idx_{i}') for i in range(num_steps)]
start = [Int(f'start_{i}') for i in range(num_steps)]
end = [Int(f'end_{i}') for i in range(num_steps)]

for i in range(num_steps):
    s.add(And(friend_idx[i] >= -1, friend_idx[i] <= 6))

travel_time_matrix = [[0 for _ in range(7)] for _ in range(7)]
for p in range(7):
    for c in range(7):
        prev_loc = friends[p]['location']
        curr_loc = friends[c]['location']
        travel_time_matrix[p][c] = travel_times[prev_loc][curr_loc]

for i in range(num_steps):
    fi = friend_idx[i]
    available_start_i = If(fi == 0, friends[0]['available_start'],
                           If(fi == 1, friends[1]['available_start'],
                              If(fi == 2, friends[2]['available_start'],
                                 If(fi == 3, friends[3]['available_start'],
                                    If(fi == 4, friends[4]['available_start'],
                                       If(fi == 5, friends[5]['available_start'],
                                          If(fi == 6, friends[6]['available_start'],
                                             -1
                                          )
                                       )
                                    )
                                 )
                              )
                           )
    available_end_i = If(fi == 0, friends[0]['available_end'],
                         If(fi == 1, friends[1]['available_end'],
                            If(fi == 2, friends[2]['available_end'],
                               If(fi == 3, friends[3]['available_end'],
                                  If(fi == 4, friends[4]['available_end'],
                                     If(fi == 5, friends[5]['available_end'],
                                        If(fi == 6, friends[6]['available_end'],
                                           -1
                                        )
                                     )
                                  )
                               )
                            )
                         )
    min_duration_i = If(fi == 0, friends[0]['min_duration'],
                        If(fi == 1, friends[1]['min_duration'],
                           If(fi == 2, friends[2]['min_duration'],
                              If(fi == 3, friends[3]['min_duration'],
                                 If(fi == 4, friends[4]['min_duration'],
                                    If(fi == 5, friends[5]['min_duration'],
                                       If(fi == 6, friends[6]['min_duration'],
                                          -1
                                       )
                                    )
                                 )
                              )
                           )
                        )
    s.add(Implies(fi != -1, start[i] >= available_start_i))
    s.add(Implies(fi != -1, end[i] <= available_end_i))
    s.add(Implies(fi != -1, end[i] - start[i] >= min_duration_i))

    if i == 0:
        travel_time_0 = If(fi == 0, travel_times['Presidio'][friends[0]['location']],
                           If(fi == 1, travel_times['Presidio'][friends[1]['location']],
                              If(fi == 2, travel_times['Presidio'][friends[2]['location']],
                                 If(fi == 3, travel_times['Presidio'][friends[3]['location']],
                                    If(fi == 4, travel_times['Presidio'][friends[4]['location']],
                                       If(fi == 5, travel_times['Presidio'][friends[5]['location']],
                                          If(fi == 6, travel_times['Presidio'][friends[6]['location']],
                                             -1
                                          )
                                       )
                                    )
                                 )
                              )
                           )
        s.add(Implies(fi != -1, start[0] >= 540 + travel_time_0))

for i in range(1, num_steps):
    fi_prev = friend_idx[i-1]
    fi_curr = friend_idx[i]
    travel_time_expr = 0
    for p in range(7):
        for c in range(7):
            travel_time_expr = If(And(fi_prev == p, fi_curr == c), travel_time_matrix[p][c], travel_time_expr)
    s.add(Implies(And(fi_prev != -1, fi_curr != -1), start[i] >= end[i-1] + travel_time_expr))

for i in range(num_steps):
    for j in range(i+1, num_steps):
        s.add(Implies(And(friend_idx[i] != -1, friend_idx[j] != -1), friend_idx[i] != friend_idx[j]))

if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(num_steps):
        fi_val = m.eval(friend_idx[i])
        if fi_val != -1:
            start_val = m.eval(start[i])
            end_val = m.eval(end[i])
            friend = friends[fi_val]
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": to_time_str(start_val),
                "end_time": to_time_str(end_val)
            })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")
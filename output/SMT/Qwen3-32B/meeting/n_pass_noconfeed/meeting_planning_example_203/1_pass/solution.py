import itertools
import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('FD', 'FW'): 10,
    ('FD', 'PH'): 13,
    ('FD', 'MD'): 17,
    ('FW', 'FD'): 11,
    ('FW', 'PH'): 12,
    ('FW', 'MD'): 22,
    ('PH', 'FD'): 13,
    ('PH', 'FW'): 13,
    ('PH', 'MD'): 15,
    ('MD', 'FD'): 17,
    ('MD', 'FW'): 22,
    ('MD', 'PH'): 16,
}

friends = {
    'Timothy': {
        'location': 'PH',
        'available_start': 540,  # 9:00 AM
        'available_end': 930,    # 3:30 PM
        'required_duration': 75
    },
    'David': {
        'location': 'FW',
        'available_start': 645,  # 10:45 AM
        'available_end': 930,
        'required_duration': 15
    },
    'Robert': {
        'location': 'MD',
        'available_start': 735,  # 12:15 PM
        'available_end': 1185,   # 7:45 PM
        'required_duration': 90
    }
}

friends_list = ['Timothy', 'David', 'Robert']

def is_permutation_feasible(perm):
    solver = z3.Solver()
    start_vars = {}
    prev_end = 540  # starting at FD at 9:00 AM
    prev_loc = 'FD'

    for friend in perm:
        loc = friends[friend]['location']
        travel_time = travel_times[(prev_loc, loc)]
        arrival = prev_end + travel_time
        s = z3.Int(f's_{friend}')
        start_vars[friend] = s
        solver.add(s >= arrival)
        solver.add(s >= friends[friend]['available_start'])
        end = s + friends[friend]['required_duration']
        solver.add(end <= friends[friend]['available_end'])
        prev_end = end
        prev_loc = loc

    if solver.check() == z3.sat:
        return True, solver.model(), start_vars
    else:
        return False, None, None

itinerary = []

for subset_size in range(len(friends_list), 0, -1):
    for subset in itertools.combinations(friends_list, subset_size):
        for perm in itertools.permutations(subset):
            feasible, model, start_vars = is_permutation_feasible(perm)
            if feasible:
                for friend in perm:
                    s = model.eval(start_vars[friend]).as_long()
                    duration = friends[friend]['required_duration']
                    e = s + duration
                    itinerary.append({
                        "action": "meet",
                        "location": friends[friend]['location'],
                        "person": friend,
                        "start_time": to_time_str(s),
                        "end_time": to_time_str(e)
                    })
                result = {
                    "itinerary": itinerary
                }
                print(json.dumps(result, indent=2))
                exit()

print(json.dumps({"itinerary": []}))
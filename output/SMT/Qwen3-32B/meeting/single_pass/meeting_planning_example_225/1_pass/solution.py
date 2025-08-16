import z3
from itertools import permutations, combinations

travel_times = {
    ('Sunset', 'North Beach'): 29,
    ('Sunset', 'Union Square'): 30,
    ('Sunset', 'Alamo Square'): 17,
    ('North Beach', 'Sunset'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
}

friend_info = {
    'Sarah': {
        'location': 'North Beach',
        'earliest': 960,
        'latest': 1095,
        'required_duration': 60,
    },
    'Jeffrey': {
        'location': 'Union Square',
        'earliest': 900,
        'latest': 1320,
        'required_duration': 75,
    },
    'Brian': {
        'location': 'Alamo Square',
        'earliest': 960,
        'latest': 1050,
        'required_duration': 75,
    },
}

start_time_sunrise = 540

best_solution = None
max_friends = 0

friends = ['Sarah', 'Jeffrey', 'Brian']

for subset_size in range(3, 0, -1):
    for subset in combinations(friends, subset_size):
        for perm in permutations(subset):
            solver = z3.Solver()
            starts = []
            ends = []
            prev_end = start_time_sunrise
            prev_location = 'Sunset'
            for i, friend in enumerate(perm):
                info = friend_info[friend]
                current_location = info['location']
                travel_time = travel_times.get((prev_location, current_location), 0)
                arrival_time = prev_end + travel_time
                start = z3.Int(f'start_{i}')
                end = z3.Int(f'end_{i}')
                starts.append(start)
                ends.append(end)
                solver.add(start >= arrival_time)
                solver.add(start >= info['earliest'])
                solver.add(end - start >= info['required_duration'])
                solver.add(end <= info['latest'])
                prev_end = end
                prev_location = current_location
            if solver.check() == z3.sat:
                model = solver.model()
                num_friends = len(perm)
                if num_friends > max_friends:
                    max_friends = num_friends
                    itinerary = []
                    for i in range(len(perm)):
                        friend_name = perm[i]
                        start_val = model[starts[i]].as_long()
                        end_val = model[ends[i]].as_long()
                        def to_time_str(minutes):
                            hours = minutes // 60
                            mins = minutes % 60
                            return f"{hours:02d}:{mins:02d}"
                        start_time = to_time_str(start_val)
                        end_time = to_time_str(end_val)
                        itinerary.append({"action": "meet", "person": friend_name, "start_time": start_time, "end_time": end_time})
                    best_solution = {"itinerary": itinerary}
print(best_solution)
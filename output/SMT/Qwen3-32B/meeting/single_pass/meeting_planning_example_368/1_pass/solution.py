import z3
import itertools

friends = [
    {'name': 'Joseph', 'location': 'Russian Hill', 'available_start': 510, 'available_end': 1155, 'duration': 60},
    {'name': 'Nancy', 'location': 'Alamo Square', 'available_start': 660, 'available_end': 960, 'duration': 90},
    {'name': 'Jason', 'location': 'North Beach', 'available_start': 1005, 'available_end': 1305, 'duration': 15},
    {'name': 'Jeffrey', 'location': 'Financial District', 'available_start': 630, 'available_end': 1005, 'duration': 45},
]

travel_times = {
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Financial District'): 19,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Financial District'): 11,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
}

for k in range(4, 0, -1):
    for subset in itertools.combinations(friends, k):
        for perm in itertools.permutations(subset):
            s = z3.Solver()
            start_times = [z3.Int(f'start_{i}') for i in range(k)]
            constraints = []
            prev_time = 540  # start at Bayview at 9:00 AM
            prev_loc = 'Bayview'
            for i in range(k):
                friend = perm[i]
                current_loc = friend['location']
                travel_time = travel_times[(prev_loc, current_loc)]
                arrival_time = prev_time + travel_time
                constraints.append(start_times[i] >= arrival_time)
                constraints.append(start_times[i] >= friend['available_start'])
                constraints.append(start_times[i] + friend['duration'] <= friend['available_end'])
                prev_time = start_times[i] + friend['duration']
                prev_loc = current_loc
            s.add(constraints)
            if s.check() == z3.sat:
                model = s.model()
                itinerary = []
                prev_time_val = 540
                prev_loc_val = 'Bayview'
                for i in range(k):
                    friend = perm[i]
                    start_val = model[start_times[i]].as_long()
                    end_val = start_val + friend['duration']
                    start_time_str = f"{start_val//60:02d}:{start_val%60:02d}"
                    end_time_str = f"{end_val//60:02d}:{end_val%60:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": start_time_str,
                        "end_time": end_time_str
                    })
                print("SOLUTION:", {"itinerary": itinerary})
                exit()

# If no solution found for any k >=1
print("SOLUTION:", {"itinerary": []})
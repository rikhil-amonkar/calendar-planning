from z3 import *
import itertools
import json

# Define travel times between locations
travel_times = {
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Alamo Square'): 10
}

# Define friend information: name, location, availability, and minimum meeting duration
friends_info = [
    {'name': 'Stephanie', 'location': 'Russian Hill', 'start_avail': 20*60, 'end_avail': 20*60+45, 'min_duration': 15},
    {'name': 'Kevin', 'location': 'Fisherman\'s Wharf', 'start_avail': 19*60+15, 'end_avail': 21*60+45, 'min_duration': 75},
    {'name': 'Robert', 'location': 'Nob Hill', 'start_avail': 7*60+45, 'end_avail': 10*60+30, 'min_duration': 90},
    {'name': 'Steven', 'location': 'Golden Gate Park', 'start_avail': 8*60+30, 'end_avail': 17*60, 'min_duration': 75},
    {'name': 'Anthony', 'location': 'Alamo Square', 'start_avail': 7*60+45, 'end_avail': 19*60+45, 'min_duration': 15},
    {'name': 'Sandra', 'location': 'Pacific Heights', 'start_avail': 14*60+45, 'end_avail': 21*60+45, 'min_duration': 45}
]

# Starting time at Haight-Ashbury: 9:00 AM (540 minutes)
n = len(friends_info)
found = False
result_itinerary = []

# Iterate over subset sizes from largest to smallest
for k in range(n, -1, -1):
    if found:
        break
    # Generate all combinations of friends of size k
    for subset in itertools.combinations(range(n), k):
        if found:
            break
        # Generate all permutations of the subset
        for perm in itertools.permutations(subset):
            s = Solver()
            starts = [Int(f'start_{i}') for i in range(k)]
            valid = True
            
            if k > 0:
                # First meeting: travel from start location to first friend
                friend0 = friends_info[perm[0]]
                tt0 = travel_times[('Haight-Ashbury', friend0['location'])]
                s.add(starts[0] >= 540 + tt0)
                s.add(starts[0] >= friend0['start_avail'])
                s.add(starts[0] + friend0['min_duration'] <= friend0['end_avail'])
                
                # Subsequent meetings
                for i in range(1, k):
                    prev_friend = friends_info[perm[i-1]]
                    curr_friend = friends_info[perm[i]]
                    tt = travel_times.get((prev_friend['location'], curr_friend['location']))
                    if tt is None:
                        valid = False
                        break
                    s.add(starts[i] >= starts[i-1] + prev_friend['min_duration'] + tt)
                    s.add(starts[i] >= curr_friend['start_avail'])
                    s.add(starts[i] + curr_friend['min_duration'] <= curr_friend['end_avail'])
            
            if not valid:
                continue
                
            if s.check() == sat:
                m = s.model()
                itinerary = []
                for i in range(k):
                    friend_idx = perm[i]
                    friend = friends_info[friend_idx]
                    start_val = m[starts[i]].as_long()
                    end_val = start_val + friend['min_duration']
                    start_hour = start_val // 60
                    start_minute = start_val % 60
                    end_hour = end_val // 60
                    end_minute = end_val % 60
                    start_str = f"{start_hour:02d}:{start_minute:02d}"
                    end_str = f"{end_hour:02d}:{end_minute:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    })
                result_itinerary = itinerary
                found = True
                break

# Output the solution
print("SOLUTION:")
print(json.dumps({"itinerary": result_itinerary}))
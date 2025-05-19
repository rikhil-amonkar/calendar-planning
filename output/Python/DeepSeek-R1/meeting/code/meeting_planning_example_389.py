import json
from itertools import permutations, chain, combinations

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

travel_times = {
    'Haight-Ashbury': {'Fisherman\'s Wharf': 23, 'Richmond District': 10, 'Mission District': 11, 'Bayview': 18},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Richmond District': 18, 'Mission District': 22, 'Bayview': 26},
    'Richmond District': {'Haight-Ashbury': 10, 'Fisherman\'s Wharf': 18, 'Mission District': 20, 'Bayview': 26},
    'Mission District': {'Haight-Ashbury': 12, 'Fisherman\'s Wharf': 22, 'Richmond District': 20, 'Bayview': 15},
    'Bayview': {'Haight-Ashbury': 19, 'Fisherman\'s Wharf': 25, 'Richmond District': 25, 'Mission District': 13}
}

friends_data = [
    {'name': 'Sarah', 'location': 'Fisherman\'s Wharf', 'window_start': '14:45', 'window_end': '17:30', 'duration': 105},
    {'name': 'Mary', 'location': 'Richmond District', 'window_start': '13:00', 'window_end': '19:15', 'duration': 75},
    {'name': 'Thomas', 'location': 'Bayview', 'window_start': '15:15', 'window_end': '18:45', 'duration': 120},
    {'name': 'Helen', 'location': 'Mission District', 'window_start': '21:45', 'window_end': '22:30', 'duration': 30}
]

def all_subsets(s):
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s)+1))

best_itinerary = []
max_count = 0
max_duration = 0

for subset in all_subsets([0, 1, 2]):
    for perm in permutations(subset):
        current_time = 540
        current_loc = 'Haight-Ashbury'
        itinerary = []
        valid = True
        
        for idx in perm:
            friend = friends_data[idx]
            if current_loc not in travel_times or friend['location'] not in travel_times[current_loc]:
                valid = False
                break
            travel = travel_times[current_loc][friend['location']]
            arrival = current_time + travel
            w_start = time_to_min(friend['window_start'])
            w_end = time_to_min(friend['window_end'])
            earliest = max(arrival, w_start)
            latest = w_end - friend['duration']
            if earliest > latest:
                valid = False
                break
            itinerary.append({
                'action': 'meet', 'location': friend['location'], 'person': friend['name'],
                'start_time': min_to_time(earliest), 'end_time': min_to_time(earliest + friend['duration'])
            })
            current_time = earliest + friend['duration']
            current_loc = friend['location']
        
        if not valid:
            continue
        
        helen = friends_data[3]
        if current_loc not in travel_times or helen['location'] not in travel_times[current_loc]:
            helen_valid = False
        else:
            travel = travel_times[current_loc][helen['location']]
            arrival = current_time + travel
            h_start = time_to_min(helen['window_start'])
            h_end = time_to_min(helen['window_end'])
            earliest_h = max(arrival, h_start)
            latest_h = h_end - helen['duration']
            helen_valid = earliest_h <= latest_h
            if helen_valid:
                itinerary.append({
                    'action': 'meet', 'location': helen['location'], 'person': helen['name'],
                    'start_time': min_to_time(earliest_h), 'end_time': min_to_time(earliest_h + helen['duration'])
                })
                current_time = earliest_h + helen['duration']
        
        count = len(perm) + (1 if helen_valid else 0)
        duration = sum(friends_data[i]['duration'] for i in perm) + (helen['duration'] if helen_valid else 0)
        
        if count > max_count or (count == max_count and duration > max_duration):
            best_itinerary = itinerary
            max_count = count
            max_duration = duration

print(json.dumps({"itinerary": best_itinerary}, indent=2))
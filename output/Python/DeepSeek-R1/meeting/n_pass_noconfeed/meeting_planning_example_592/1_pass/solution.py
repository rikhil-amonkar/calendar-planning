import itertools
import json

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{int(hours)}:{minutes:02d}"

# Travel times dictionary
travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17
    }
}

# Friends data in minutes
friends = [
    {'name': 'James', 'location': 'Pacific Heights', 'start_avail': 1200, 'end_avail': 1320, 'min_duration': 120},
    {'name': 'Robert', 'location': 'Chinatown', 'start_avail': 735, 'end_avail': 1005, 'min_duration': 90},
    {'name': 'Jeffrey', 'location': 'Union Square', 'start_avail': 570, 'end_avail': 930, 'min_duration': 120},
    {'name': 'Carol', 'location': 'Mission District', 'start_avail': 1095, 'end_avail': 1335, 'min_duration': 15},
    {'name': 'Mark', 'location': 'Golden Gate Park', 'start_avail': 690, 'end_avail': 1065, 'min_duration': 15},
    {'name': 'Sandra', 'location': 'Nob Hill', 'start_avail': 480, 'end_avail': 930, 'min_duration': 15}
]

# Start at North Beach at 9:00 AM (540 minutes)
start_time = 540
start_loc = "North Beach"

# Generate all permutations of friends
all_permutations = list(itertools.permutations(friends))

best_count = -1
best_itinerary = None

for perm in all_permutations:
    current_time = start_time
    current_loc = start_loc
    itinerary = []
    count = 0
    
    for friend in perm:
        loc = friend['location']
        travel_time = travel_times[current_loc][loc]
        arrival_time = current_time + travel_time
        start_meet = max(arrival_time, friend['start_avail'])
        end_meet = start_meet + friend['min_duration']
        
        if end_meet <= friend['end_avail']:
            itinerary.append({
                'person': friend['name'],
                'location': loc,
                'start': start_meet,
                'end': end_meet
            })
            current_time = end_meet
            current_loc = loc
            count += 1
        else:
            continue
    
    if count > best_count:
        best_count = count
        best_itinerary = itinerary

# Format the best itinerary
formatted_itinerary = []
if best_itinerary is not None:
    for event in best_itinerary:
        formatted_itinerary.append({
            "action": "meet",
            "location": event['location'],
            "person": event['person'],
            "start_time": min_to_time(event['start']),
            "end_time": min_to_time(event['end'])
        })

# Output as JSON
result = {
    "itinerary": formatted_itinerary
}

print(json.dumps(result))
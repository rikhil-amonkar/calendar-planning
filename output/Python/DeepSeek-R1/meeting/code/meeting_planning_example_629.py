import json
import itertools

# Define travel times
travel_times = {
    'Russian Hill': {
        'Presidio': 14,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'Richmond District': 14,
        'Fisherman\'s Wharf': 7,
        'Golden Gate Park': 21,
        'Bayview': 23
    },
    'Presidio': {
        'Russian Hill': 14,
        'Chinatown': 21,
        'Pacific Heights': 11,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Chinatown': {
        'Russian Hill': 7,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Richmond District': 20,
        'Fisherman\'s Wharf': 8,
        'Golden Gate Park': 23,
        'Bayview': 22
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'Presidio': 11,
        'Chinatown': 11,
        'Richmond District': 12,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15,
        'Bayview': 22
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Presidio': 7,
        'Chinatown': 20,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Bayview': 26
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'Richmond District': 18,
        'Golden Gate Park': 25,
        'Bayview': 26
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23
    },
    'Bayview': {
        'Russian Hill': 23,
        'Presidio': 31,
        'Chinatown': 18,
        'Pacific Heights': 23,
        'Richmond District': 25,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    }
}

# Define friends' availability
friends = [
    {'name': 'Matthew', 'location': 'Presidio', 'start': 11 * 60, 'end': 21 * 60, 'duration': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start': 9 * 60 + 15, 'end': 18 * 60 + 45, 'duration': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': 14 * 60 + 15, 'end': 17 * 60, 'duration': 15},
    {'name': 'Helen', 'location': 'Richmond District', 'start': 19 * 60 + 45, 'end': 22 * 60, 'duration': 60},
    {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': 21 * 60 + 15, 'end': 22 * 60 + 15, 'duration': 60},
    {'name': 'Kimberly', 'location': 'Golden Gate Park', 'start': 13 * 60, 'end': 16 * 60 + 30, 'duration': 120},
    {'name': 'Kenneth', 'location': 'Bayview', 'start': 14 * 60 + 30, 'end': 18 * 60, 'duration': 60},
]

def format_time(minutes):
    return f"{minutes // 60}:{minutes % 60:02d}"

best_count = 0
best_duration = 0
best_itinerary = []

# Check all possible permutations
for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        current_time = 540  # Start at 9:00 AM
        current_loc = 'Russian Hill'
        itinerary = []
        valid = True
        
        for friend in perm:
            # Get travel time
            if friend['location'] not in travel_times[current_loc]:
                valid = False
                break
            travel = travel_times[current_loc][friend['location']]
            arrival = current_time + travel
            start = max(arrival, friend['start'])
            end = start + friend['duration']
            
            if end > friend['end']:
                valid = False
                break
            
            itinerary.append((friend, start, end))
            current_time = end
            current_loc = friend['location']
        
        if valid:
            count = len(perm)
            duration = sum(f['duration'] for f, _, _ in itinerary)
            if (count > best_count) or (count == best_count and duration > best_duration):
                best_count = count
                best_duration = duration
                best_itinerary = itinerary

# Convert to JSON format
result = {"itinerary": []}
for entry in best_itinerary:
    friend, start, end = entry
    result["itinerary"].append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": format_time(start),
        "end_time": format_time(end)
    })

print(json.dumps(result, indent=2))
import itertools
import json

friends = [
    {'name': 'Paul', 'location': 'Nob Hill', 'start': 975, 'end': 1275, 'duration': 60},
    {'name': 'Carol', 'location': 'Union Square', 'start': 1080, 'end': 1215, 'duration': 120},
    {'name': 'Patricia', 'location': 'Chinatown', 'start': 1200, 'end': 1290, 'duration': 75},
    {'name': 'Karen', 'location': 'The Castro', 'start': 1020, 'end': 1140, 'duration': 45},
    {'name': 'Nancy', 'location': 'Presidio', 'start': 705, 'end': 1320, 'duration': 30},
    {'name': 'Jeffrey', 'location': 'Pacific Heights', 'start': 1200, 'end': 1245, 'duration': 45},
    {'name': 'Matthew', 'location': 'Russian Hill', 'start': 945, 'end': 1305, 'duration': 75},
]

travel_time = {
    'Bayview': {
        'Nob Hill': 20, 'Union Square': 17, 'Chinatown': 18, 'The Castro': 20,
        'Presidio': 31, 'Pacific Heights': 23, 'Russian Hill': 23
    },
    'Nob Hill': {
        'Bayview': 19, 'Union Square': 7, 'Chinatown': 6, 'The Castro': 17,
        'Presidio': 17, 'Pacific Heights': 8, 'Russian Hill': 5
    },
    'Union Square': {
        'Bayview': 15, 'Nob Hill': 9, 'Chinatown': 7, 'The Castro': 19,
        'Presidio': 24, 'Pacific Heights': 15, 'Russian Hill': 13
    },
    'Chinatown': {
        'Bayview': 22, 'Nob Hill': 8, 'Union Square': 7, 'The Castro': 22,
        'Presidio': 19, 'Pacific Heights': 10, 'Russian Hill': 7
    },
    'The Castro': {
        'Bayview': 19, 'Nob Hill': 16, 'Union Square': 19, 'Chinatown': 20,
        'Presidio': 20, 'Pacific Heights': 16, 'Russian Hill': 18
    },
    'Presidio': {
        'Bayview': 31, 'Nob Hill': 18, 'Union Square': 22, 'Chinatown': 21,
        'The Castro': 21, 'Pacific Heights': 11, 'Russian Hill': 14
    },
    'Pacific Heights': {
        'Bayview': 22, 'Nob Hill': 8, 'Union Square': 12, 'Chinatown': 11,
        'The Castro': 16, 'Presidio': 11, 'Russian Hill': 7
    },
    'Russian Hill': {
        'Bayview': 23, 'Nob Hill': 5, 'Union Square': 11, 'Chinatown': 9,
        'The Castro': 21, 'Presidio': 14, 'Pacific Heights': 7
    }
}

best_count = 0
best_itinerary = []
best_end_time = float('inf')

for perm in itertools.permutations(friends):
    current_location = 'Bayview'
    current_time = 540  # 9:00 AM
    itinerary = []
    count = 0
    for friend in perm:
        tt = travel_time[current_location].get(friend['location'], 0)
        arrival = current_time + tt
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            continue
        itinerary.append((friend, start, end))
        current_location = friend['location']
        current_time = end
        count += 1
    if count > best_count or (count == best_count and current_time < best_end_time):
        best_count = count
        best_end_time = current_time
        best_itinerary = itinerary

formatted = []
for item in best_itinerary:
    friend, start, end = item
    start_h, start_m = divmod(start, 60)
    end_h, end_m = divmod(end, 60)
    start_str = f"{start_h}:{start_m:02d}".replace(":00", ":0").replace(":0", ":") if start_m <10 else f"{start_h}:{start_m}"
    end_str = f"{end_h}:{end_m:02d}".replace(":00", ":0").replace(":0", ":") if end_m <10 else f"{end_h}:{end_m}"
    formatted.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_str,
        "end_time": end_str
    })

print(json.dumps({"itinerary": formatted}, indent=2))
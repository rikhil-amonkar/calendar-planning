import itertools
import json

def format_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Mission District': {'The Castro':7, 'Nob Hill':12, 'Presidio':25, 'Marina District':19, 'Pacific Heights':16, 'Golden Gate Park':17, 'Chinatown':16, 'Richmond District':20},
    'The Castro': {'Mission District':7, 'Nob Hill':16, 'Presidio':20, 'Marina District':21, 'Pacific Heights':16, 'Golden Gate Park':11, 'Chinatown':22, 'Richmond District':16},
    'Nob Hill': {'Mission District':13, 'The Castro':17, 'Presidio':17, 'Marina District':11, 'Pacific Heights':8, 'Golden Gate Park':17, 'Chinatown':6, 'Richmond District':14},
    'Presidio': {'Mission District':26, 'The Castro':21, 'Nob Hill':18, 'Marina District':11, 'Pacific Heights':11, 'Golden Gate Park':12, 'Chinatown':21, 'Richmond District':7},
    'Marina District': {'Mission District':20, 'The Castro':22, 'Nob Hill':12, 'Presidio':10, 'Pacific Heights':7, 'Golden Gate Park':18, 'Chinatown':15, 'Richmond District':11},
    'Pacific Heights': {'Mission District':15, 'The Castro':16, 'Nob Hill':8, 'Presidio':11, 'Marina District':6, 'Golden Gate Park':15, 'Chinatown':11, 'Richmond District':12},
    'Golden Gate Park': {'Mission District':17, 'The Castro':13, 'Nob Hill':20, 'Presidio':11, 'Marina District':16, 'Pacific Heights':16, 'Chinatown':23, 'Richmond District':7},
    'Chinatown': {'Mission District':17, 'The Castro':22, 'Nob Hill':9, 'Presidio':19, 'Marina District':12, 'Pacific Heights':10, 'Golden Gate Park':23, 'Richmond District':20},
    'Richmond District': {'Mission District':20, 'The Castro':16, 'Nob Hill':17, 'Presidio':7, 'Marina District':9, 'Pacific Heights':10, 'Golden Gate Park':9, 'Chinatown':20}
}

friends = [
    {'name': 'Lisa', 'location': 'The Castro', 'start': 1155, 'end': 1290, 'duration': 120},
    {'name': 'Daniel', 'location': 'Nob Hill', 'start': 495, 'end': 660, 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Presidio', 'start': 1290, 'end': 1335, 'duration': 45},
    {'name': 'Steven', 'location': 'Marina District', 'start': 990, 'end': 1245, 'duration': 90},
    {'name': 'Timothy', 'location': 'Pacific Heights', 'start': 720, 'end': 1080, 'duration': 90},
    {'name': 'Kevin', 'location': 'Chinatown', 'start': 720, 'end': 1140, 'duration': 30},
    {'name': 'Betty', 'location': 'Richmond District', 'start': 795, 'end': 945, 'duration': 30},
    {'name': 'Ashley', 'location': 'Golden Gate Park', 'start': 1245, 'end': 1305, 'duration': 60}
]

best_count = 0
best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Mission District'
    current_time = 540
    itinerary = []
    scheduled = set()
    for friend in perm:
        if friend['name'] in scheduled:
            continue
        to_loc = friend['location']
        travel_time = travel_times[current_location].get(to_loc, float('inf'))
        arrival = current_time + travel_time
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            continue
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': format_time(start).replace(':0', ':') if format_time(start).endswith(':00') else format_time(start).lstrip('0'),
            'end_time': format_time(end).replace(':0', ':') if format_time(end).endswith(':00') else format_time(end).lstrip('0')
        })
        scheduled.add(friend['name'])
        current_time = end
        current_location = to_loc
    if len(scheduled) > best_count:
        best_count = len(scheduled)
        best_itinerary = itinerary

print(json.dumps({'itinerary': best_itinerary}, indent=2))
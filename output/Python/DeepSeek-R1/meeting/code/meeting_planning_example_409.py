import itertools
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'start': 15 * 60 + 30,
        'end': 18 * 60 + 30,
        'duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Golden Gate Park',
        'start': 18 * 60 + 30,
        'end': 21 * 60 + 45,
        'duration': 30
    },
    {
        'name': 'Laura',
        'location': 'Nob Hill',
        'start': 8 * 60 + 45,
        'end': 16 * 60 + 15,
        'duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'start': 18 * 60 + 45,
        'end': 21 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Embarcadero',
        'start': 17 * 60 + 30,
        'end': 22 * 60 + 0,
        'duration': 45
    }
]

travel_times = {
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

best_itinerary = []
best_count = 0
best_time = float('inf')

for perm in itertools.permutations(friends):
    current_location = 'Fisherman\'s Wharf'
    current_time = 540
    itinerary = []
    for friend in perm:
        if current_location == friend['location']:
            travel_duration = 0
        else:
            try:
                travel_duration = travel_times[current_location][friend['location']]
            except KeyError:
                continue
        arrival_time = current_time + travel_duration
        latest_start = friend['end'] - friend['duration']
        if arrival_time > latest_start:
            continue
        start_time = max(arrival_time, friend['start'])
        if start_time > latest_start:
            continue
        end_time = start_time + friend['duration']
        if end_time > friend['end']:
            continue
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_time,
            'end_time': end_time
        })
        current_location = friend['location']
        current_time = end_time
    if len(itinerary) > best_count or (len(itinerary) == best_count and current_time < best_time):
        best_count = len(itinerary)
        best_itinerary = itinerary.copy()
        best_time = current_time

formatted_itinerary = []
for item in best_itinerary:
    formatted_item = {
        'action': 'meet',
        'location': item['location'],
        'person': item['person'],
        'start_time': minutes_to_time(item['start_time']),
        'end_time': minutes_to_time(item['end_time'])
    }
    formatted_itinerary.append(formatted_item)

print(json.dumps({'itinerary': formatted_itinerary}, indent=2))
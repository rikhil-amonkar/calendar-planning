import itertools
import json

def min_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Emily',
        'location': 'Presidio',
        'start': 16 * 60 + 15,
        'end': 21 * 60,
        'duration': 105
    },
    {
        'name': 'Joseph',
        'location': 'Richmond District',
        'start': 17 * 60 + 15,
        'end': 22 * 60,
        'duration': 120
    },
    {
        'name': 'Melissa',
        'location': 'Financial District',
        'start': 15 * 60 + 45,
        'end': 21 * 60 + 45,
        'duration': 75
    }
]

travel_times = {
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Richmond District': 18,
        'Financial District': 11
    },
    'Presidio': {
        'Fisherman\'s Wharf': 19,
        'Richmond District': 7,
        'Financial District': 23
    },
    'Richmond District': {
        'Fisherman\'s Wharf': 18,
        'Presidio': 7,
        'Financial District': 22
    },
    'Financial District': {
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Richmond District': 21
    }
}

best_schedule = None

for perm in itertools.permutations(friends):
    current_location = 'Fisherman\'s Wharf'
    current_time = 540
    schedule = []
    valid = True
    for friend in perm:
        if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
            valid = False
            break
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        start_meet = max(arrival_time, friend['start'])
        end_meet = start_meet + friend['duration']
        if end_meet > friend['end']:
            valid = False
            break
        schedule.append((friend, start_meet, end_meet))
        current_time = end_meet
        current_location = friend['location']
    if valid:
        best_schedule = schedule
        break

if best_schedule:
    itinerary = []
    for entry in best_schedule:
        friend = entry[0]
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": min_to_time_str(entry[1]),
            "end_time": min_to_time_str(entry[2])
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')
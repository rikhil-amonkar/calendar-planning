import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Financial District': {'Russian Hill': 10, 'Sunset District': 31, 'North Beach': 7, 'The Castro': 23, 'Golden Gate Park': 23},
    'Russian Hill': {'Financial District': 11, 'Sunset District': 23, 'North Beach': 5, 'The Castro': 21, 'Golden Gate Park': 21},
    'Sunset District': {'Financial District': 30, 'Russian Hill': 24, 'North Beach': 29, 'The Castro': 17, 'Golden Gate Park': 11},
    'North Beach': {'Financial District': 8, 'Russian Hill': 4, 'Sunset District': 27, 'The Castro': 22, 'Golden Gate Park': 22},
    'The Castro': {'Financial District': 20, 'Russian Hill': 18, 'Sunset District': 17, 'North Beach': 20, 'Golden Gate Park': 11},
    'Golden Gate Park': {'Financial District': 26, 'Russian Hill': 19, 'Sunset District': 10, 'North Beach': 24, 'The Castro': 13}
}

friends = [
    {'name': 'Patricia', 'location': 'Sunset District', 'start': 555, 'end': 1320, 'duration': 60},
    {'name': 'Laura', 'location': 'North Beach', 'start': 750, 'end': 765, 'duration': 15},
    {'name': 'Ronald', 'location': 'Russian Hill', 'start': 825, 'end': 1035, 'duration': 105},
    {'name': 'Emily', 'location': 'The Castro', 'start': 975, 'end': 1110, 'duration': 60},
    {'name': 'Mary', 'location': 'Golden Gate Park', 'start': 900, 'end': 990, 'duration': 60}
]

current_time = 540  # 9:00 AM
current_location = 'Financial District'
itinerary = []
met = set()

# Meet Patricia
friend = next(f for f in friends if f['name'] == 'Patricia')
travel = travel_times[current_location][friend['location']]
arrival = current_time + travel
start = max(arrival, friend['start'])
if start + friend['duration'] <= friend['end']:
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start),
        'end_time': minutes_to_time(start + friend['duration'])
    })
    met.add(friend['name'])
    current_time = start + friend['duration']
    current_location = friend['location']

# Meet Laura
friend = next(f for f in friends if f['name'] == 'Laura')
travel = travel_times[current_location][friend['location']]
arrival = current_time + travel
start = max(arrival, friend['start'])
if start + friend['duration'] <= friend['end']:
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start),
        'end_time': minutes_to_time(start + friend['duration'])
    })
    met.add(friend['name'])
    current_time = start + friend['duration']
    current_location = friend['location']

# Meet Ronald
friend = next(f for f in friends if f['name'] == 'Ronald')
travel = travel_times[current_location][friend['location']]
arrival = current_time + travel
start = max(arrival, friend['start'])
if start + friend['duration'] <= friend['end']:
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start),
        'end_time': minutes_to_time(start + friend['duration'])
    })
    met.add(friend['name'])
    current_time = start + friend['duration']
    current_location = friend['location']

# Meet Emily
friend = next(f for f in friends if f['name'] == 'Emily')
travel = travel_times[current_location][friend['location']]
arrival = current_time + travel
start = max(arrival, friend['start'])
if start + friend['duration'] <= friend['end']:
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start),
        'end_time': minutes_to_time(start + friend['duration'])
    })
    met.add(friend['name'])
    current_time = start + friend['duration']
    current_location = friend['location']

output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))
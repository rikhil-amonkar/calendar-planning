import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}".replace(":0", ":")

friends = [
    {'name': 'Brian', 'location': 'Marina District', 'start': 735, 'end': 1080, 'duration': 60},
    {'name': 'Thomas', 'location': 'Fisherman\'s Wharf', 'start': 810, 'end': 1140, 'duration': 30},
    {'name': 'Nancy', 'location': 'North Beach', 'start': 885, 'end': 1200, 'duration': 15},
    {'name': 'Jessica', 'location': 'Nob Hill', 'start': 990, 'end': 1125, 'duration': 120},
    {'name': 'Mary', 'location': 'Union Square', 'start': 1005, 'end': 1290, 'duration': 60},
    {'name': 'Matthew', 'location': 'Bayview', 'start': 1155, 'end': 1320, 'duration': 120}
]

travel_times = {
    ('Embarcadero', 'Marina District'): 12,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('North Beach', 'Nob Hill'): 7,
    ('Nob Hill', 'Union Square'): 7,
    ('Union Square', 'Bayview'): 15
}

current_location = 'Embarcadero'
current_time = 540
itinerary = []

for friend in friends:
    to_loc = friend['location']
    travel_time = travel_times.get((current_location, to_loc), 0)
    arrival = current_time + travel_time
    start = max(arrival, friend['start'])
    end = start + friend['duration']
    if end > friend['end']:
        continue
    itinerary.append({
        'action': 'meet',
        'location': to_loc,
        'person': friend['name'],
        'start_time': minutes_to_time(start),
        'end_time': minutes_to_time(end)
    })
    current_time = end
    current_location = to_loc

print(json.dumps({'itinerary': itinerary}, indent=2))
import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours}:{minutes_part:02d}"

travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Financial District': 30
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Presidio': 18,
        'Financial District': 17
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Presidio': 14,
        'Financial District': 11
    },
    'Presidio': {
        'Sunset District': 15,
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Financial District': 23
    },
    'Financial District': {
        'Sunset District': 31,
        'Alamo Square': 17,
        'Russian Hill': 10,
        'Presidio': 22
    }
}

friends = [
    {'name': 'Kevin', 'location': 'Alamo Square', 'start': 495, 'end': 1290, 'duration': 75},
    {'name': 'Kimberly', 'location': 'Russian Hill', 'start': 525, 'end': 750, 'duration': 30},
    {'name': 'Joseph', 'location': 'Presidio', 'start': 1110, 'end': 1155, 'duration': 45},
    {'name': 'Thomas', 'location': 'Financial District', 'start': 1140, 'end': 1305, 'duration': 45}
]

perms = list(itertools.permutations(friends))

start_time = 540
start_location = 'Sunset District'
max_count = 0
best_itinerary = None

for perm in perms:
    current_location = start_location
    current_time = start_time
    itinerary = []
    count = 0
    for friend in perm:
        travel_duration = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_duration
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end <= friend['end']:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            count += 1
            current_time = meeting_end
            current_location = friend['location']
    if count > max_count:
        max_count = count
        best_itinerary = itinerary
    if max_count == 4:
        break

if best_itinerary is None:
    best_itinerary = []

result = {"itinerary": best_itinerary}
print(json.dumps(result))
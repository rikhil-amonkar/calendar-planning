import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours}:{minutes_part:02d}"

travel_times = {
    'Union Square': {'Mission District': 14, 'Bayview': 15, 'Sunset District': 26},
    'Mission District': {'Union Square': 15, 'Bayview': 15, 'Sunset District': 24},
    'Bayview': {'Union Square': 17, 'Mission District': 13, 'Sunset District': 23},
    'Sunset District': {'Union Square': 30, 'Mission District': 24, 'Bayview': 22}
}

friends = [
    {'name': 'Carol', 'location': 'Sunset District', 'start_available': 10*60+15, 'end_available': 11*60+45, 'min_duration': 30},
    {'name': 'Karen', 'location': 'Bayview', 'start_available': 12*60+45, 'end_available': 15*60+0, 'min_duration': 120},
    {'name': 'Rebecca', 'location': 'Mission District', 'start_available': 11*60+30, 'end_available': 20*60+15, 'min_duration': 120}
]

start_time_minutes = 9*60
start_location = 'Union Square'

best_count = 0
best_itinerary = None

for perm in itertools.permutations(friends):
    current_time = start_time_minutes
    current_loc = start_location
    itinerary = []
    valid = True
    for friend in perm:
        if current_loc != friend['location']:
            tt = travel_times[current_loc][friend['location']]
            current_time += tt
        if current_time < friend['start_available']:
            current_time = friend['start_available']
        if current_time + friend['min_duration'] <= friend['end_available']:
            end_meeting = current_time + friend['min_duration']
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(current_time),
                'end_time': minutes_to_time(end_meeting)
            })
            current_time = end_meeting
            current_loc = friend['location']
        else:
            valid = False
            break
    if valid:
        count = len(itinerary)
        if count > best_count:
            best_count = count
            best_itinerary = itinerary
            if best_count == len(friends):
                break

if best_itinerary is None:
    best_itinerary = []

result = {"itinerary": best_itinerary}
print(json.dumps(result))
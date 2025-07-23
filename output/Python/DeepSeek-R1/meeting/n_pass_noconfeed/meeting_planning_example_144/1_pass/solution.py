import json
from itertools import permutations

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    'The Castro': {
        'Mission District': 7,
        'Financial District': 20
    },
    'Mission District': {
        'The Castro': 7,
        'Financial District': 17
    },
    'Financial District': {
        'The Castro': 23,
        'Mission District': 17
    }
}

start_location = 'The Castro'
start_time_str = '9:00'
start_time_minutes = time_to_minutes(start_time_str)

laura_location = 'Mission District'
laura_start_str = '12:15'
laura_end_str = '19:45'
laura_duration = 75

anthony_location = 'Financial District'
anthony_start_str = '12:30'
anthony_end_str = '14:45'
anthony_duration = 30

friends = [
    {
        'name': 'Laura',
        'location': laura_location,
        'start': time_to_minutes(laura_start_str),
        'end': time_to_minutes(laura_end_str),
        'duration': laura_duration
    },
    {
        'name': 'Anthony',
        'location': anthony_location,
        'start': time_to_minutes(anthony_start_str),
        'end': time_to_minutes(anthony_end_str),
        'duration': anthony_duration
    }
]

orders = list(permutations([0, 1], 2))
all_candidates = []

for order in orders:
    current_location = start_location
    current_time = start_time_minutes
    total_travel = 0
    events = []
    feasible = True
    for idx in order:
        friend = friends[idx]
        try:
            t = travel_times[current_location][friend['location']]
        except KeyError:
            feasible = False
            break
        total_travel += t
        departure_time = max(current_time, friend['start'] - t)
        arrival_time = departure_time + t
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end']:
            feasible = False
            break
        event = {
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        }
        events.append(event)
        current_location = friend['location']
        current_time = meeting_end
    if feasible:
        all_candidates.append({
            'num_meetings': 2,
            'travel_time': total_travel,
            'events': events
        })

if all_candidates:
    all_candidates.sort(key=lambda x: x['travel_time'])
    best_candidate = all_candidates[0]
    itinerary = best_candidate['events']
else:
    one_candidates = []
    for friend in friends:
        try:
            t = travel_times[start_location][friend['location']]
        except KeyError:
            continue
        departure_time = max(start_time_minutes, friend['start'] - t)
        arrival_time = departure_time + t
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end']:
            continue
        event = {
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        }
        candidate = {
            'num_meetings': 1,
            'travel_time': t,
            'events': [event]
        }
        one_candidates.append(candidate)
    if one_candidates:
        one_candidates.sort(key=lambda x: x['travel_time'])
        best_one_candidate = one_candidates[0]
        itinerary = best_one_candidate['events']
    else:
        itinerary = []

result = {
    "itinerary": itinerary
}
print(json.dumps(result))
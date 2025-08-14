import json
from itertools import permutations

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Union Square'): 22,
}

friends = [
    {
        'name': 'Richard',
        'location': 'Union Square',
        'available_start': '8:45',
        'available_end': '13:00',
        'required_duration': 120,
    },
    {
        'name': 'Charles',
        'location': 'Presidio',
        'available_start': '9:45',
        'available_end': '13:00',
        'required_duration': 120,
    },
]

best_itinerary = []
best_count = 0

initial_time = time_str_to_minutes('9:00')
initial_location = 'Bayview'

for perm in permutations(friends):
    current_time = initial_time
    current_location = initial_location
    itinerary = []
    for friend in perm:
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            break
        current_time += travel_time
        friend_start = time_str_to_minutes(friend['available_start'])
        start_time = max(current_time, friend_start)
        required_duration = friend['required_duration']
        end_time = start_time + required_duration
        friend_end = time_str_to_minutes(friend['available_end'])
        if end_time > friend_end:
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(start_time),
            'end_time': minutes_to_time_str(end_time),
        })
        current_time = end_time
        current_location = friend['location']
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))
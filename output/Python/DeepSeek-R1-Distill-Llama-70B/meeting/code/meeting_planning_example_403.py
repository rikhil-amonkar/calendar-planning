import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(mins):
    hours = mins // 60
    mins = mins % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20
}

friends = [
    {
        'name': 'Andrew',
        'location': 'Golden Gate Park',
        'available_start': '11:45',
        'available_end': '14:30',
        'required_duration': 75
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'available_start': '16:15',
        'available_end': '18:45',
        'required_duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'available_start': '17:30',
        'available_end': '19:15',
        'required_duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Chinatown',
        'available_start': '09:45',
        'available_end': '21:30',
        'required_duration': 90
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'available_start': '08:30',
        'available_end': '14:15',
        'required_duration': 30
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Union Square'

best_itinerary = []

for perm in permutations(friends):
    itinerary = []
    temp_time = current_time
    temp_loc = current_location
    valid = True

    for friend in perm:
        travel = travel_times.get((temp_loc, friend['location']), None)
        if travel is None:
            valid = False
            break
        arrival_time = temp_time + travel

        avail_start = time_to_minutes(friend['available_start'])
        avail_end = time_to_minutes(friend['available_end'])

        start_time = max(arrival_time, avail_start)
        end_time = start_time + friend['required_duration']

        if end_time > avail_end:
            valid = False
            break

        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })

        temp_time = end_time
        temp_loc = friend['location']

    if valid and len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

result = {'itinerary': best_itinerary}
print(json.dumps(result))
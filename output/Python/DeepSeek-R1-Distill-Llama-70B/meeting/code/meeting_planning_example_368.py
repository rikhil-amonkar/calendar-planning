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
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Financial District'): 19,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Financial District'): 11,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7
}

friends = [
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'available_start': '08:30',
        'available_end': '19:15',
        'required_duration': 60
    },
    {
        'name': 'Nancy',
        'location': 'Alamo Square',
        'available_start': '11:00',
        'available_end': '16:00',
        'required_duration': 90
    },
    {
        'name': 'Jason',
        'location': 'North Beach',
        'available_start': '16:45',
        'available_end': '21:45',
        'required_duration': 15
    },
    {
        'name': 'Jeffrey',
        'location': 'Financial District',
        'available_start': '10:30',
        'available_end': '15:45',
        'required_duration': 45
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Bayview'

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
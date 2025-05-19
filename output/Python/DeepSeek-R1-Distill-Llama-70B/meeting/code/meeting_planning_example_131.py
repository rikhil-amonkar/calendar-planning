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
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Presidio'): 10
}

friends = [
    {
        'name': 'Jason',
        'location': 'Presidio',
        'available_start': '10:00',
        'available_end': '16:15',
        'required_duration': 90
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': '15:30',
        'available_end': '16:45',
        'required_duration': 45
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Pacific Heights'

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
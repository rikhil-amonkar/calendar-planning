import itertools
import json

def parse_time(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def min_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02}"

travel_times = {
    'Russian Hill': {'Nob Hill': 5, 'Mission District': 16, 'Embarcadero': 8},
    'Nob Hill': {'Russian Hill': 5, 'Mission District': 13, 'Embarcadero': 9},
    'Mission District': {'Russian Hill': 15, 'Nob Hill': 12, 'Embarcadero': 19},
    'Embarcadero': {'Russian Hill': 8, 'Nob Hill': 10, 'Mission District': 20},
}

friends = [
    {
        'name': 'Patricia',
        'location': 'Nob Hill',
        'available_start': parse_time('18:30'),
        'available_end': parse_time('21:45'),
        'duration': 90
    },
    {
        'name': 'Ashley',
        'location': 'Mission District',
        'available_start': parse_time('20:30'),
        'available_end': parse_time('21:15'),
        'duration': 45
    },
    {
        'name': 'Timothy',
        'location': 'Embarcadero',
        'available_start': parse_time('9:45'),
        'available_end': parse_time('17:45'),
        'duration': 120
    }
]

best_itinerary = []
max_friends = 0
best_end_time = float('inf')

for order in itertools.permutations(friends):
    current_location = 'Russian Hill'
    current_time = parse_time('9:00')
    itinerary = []
    possible = True
    for friend in order:
        to_loc = friend['location']
        travel_time = travel_times[current_location][to_loc]
        arrival = current_time + travel_time
        start = max(arrival, friend['available_start'])
        end = start + friend['duration']
        if end > friend['available_end']:
            possible = False
            break
        itinerary.append({
            "action": "meet",
            "location": to_loc,
            "person": friend['name'],
            "start_time": min_to_time(start),
            "end_time": min_to_time(end)
        })
        current_time = end
        current_location = to_loc
    if possible:
        num = len(order)
        if num > max_friends or (num == max_friends and current_time < best_end_time):
            max_friends = num
            best_itinerary = itinerary
            best_end_time = current_time

print(json.dumps({"itinerary": best_itinerary}, indent=2))
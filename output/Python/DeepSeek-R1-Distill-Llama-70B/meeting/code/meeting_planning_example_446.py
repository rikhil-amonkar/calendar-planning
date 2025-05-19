import itertools
import json

travel_times = {
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Union Square'): 21,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Chinatown'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union Square'): 7,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Union Square'): 17,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Bayview'): 15,
}

friends = [
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'start_time': 13 * 60 + 15,  # 1:15 PM
        'end_time': 16 * 60 + 45,    # 4:45 PM
        'duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start_time': 12 * 60 + 15,  # 12:15 PM
        'end_time': 20 * 60 + 15,    # 8:15 PM
        'duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'start_time': 13 * 60 + 15,  # 1:15 PM
        'end_time': 16 * 60 + 45,    # 4:45 PM
        'duration': 75
    },
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'start_time': 9 * 60 + 30,   # 9:30 AM
        'end_time': 13 * 60 + 30,    # 1:30 PM
        'duration': 30
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'start_time': 19 * 60 + 30,  # 7:30 PM
        'end_time': 21 * 60 + 15,    # 9:15 PM
        'duration': 75
    },
]

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Richmond District'
    itinerary = []
    for friend in perm:
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            break
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['start_time'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end_time']:
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': convert_minutes_to_time(meeting_start),
            'end_time': convert_minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    if len(itinerary) > max_met:
        max_met = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))
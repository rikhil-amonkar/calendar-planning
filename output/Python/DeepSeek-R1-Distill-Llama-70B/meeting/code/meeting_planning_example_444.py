import itertools
import json

travel_times = {
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

friends = [
    {
        'name': 'Ronald',
        'location': 'Russian Hill',
        'start_time': 13 * 60 + 45,  # 1:45 PM
        'end_time': 17 * 60 + 15,    # 5:15 PM
        'duration': 105
    },
    {
        'name': 'Patricia',
        'location': 'Sunset District',
        'start_time': 9 * 60 + 15,   # 9:15 AM
        'end_time': 22 * 60 + 0,     # 10:00 PM
        'duration': 60
    },
    {
        'name': 'Laura',
        'location': 'North Beach',
        'start_time': 12 * 60 + 30,  # 12:30 PM
        'end_time': 12 * 60 + 45,    # 12:45 PM
        'duration': 15
    },
    {
        'name': 'Emily',
        'location': 'The Castro',
        'start_time': 16 * 60 + 15,  # 4:15 PM
        'end_time': 18 * 60 + 30,    # 6:30 PM
        'duration': 60
    },
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'start_time': 15 * 60 + 0,   # 3:00 PM
        'end_time': 16 * 60 + 30,    # 4:30 PM
        'duration': 60
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
    current_location = 'Financial District'
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
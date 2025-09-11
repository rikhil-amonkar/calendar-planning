import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

friends = [
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'available_start': 19 * 60,
        'available_end': 21 * 60,
        'min_duration': 15
    },
    {
        'name': 'Margaret',
        'location': 'Financial District',
        'available_start': 16 * 60 + 30,
        'available_end': 20 * 60 + 15,
        'min_duration': 75
    },
    {
        'name': 'Ronald',
        'location': 'North Beach',
        'available_start': 18 * 60 + 30,
        'available_end': 19 * 60 + 30,
        'min_duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'The Castro',
        'available_start': 13 * 60 + 45,
        'available_end': 21 * 60 + 15,
        'min_duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'available_start': 11 * 60 + 15,
        'available_end': 14 * 60 + 30,
        'min_duration': 120
    }
]

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Nob Hill'
    itinerary = []
    for friend in perm:
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            continue
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        min_duration = friend['min_duration']
        start = max(arrival_time, available_start)
        end = start + min_duration
        if end <= available_end:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = friend['location']
        else:
            pass  # Skip this friend
    if len(itinerary) > max_met:
        max_met = len(itinerary)
        best_itinerary = itinerary

print(json.dumps({"itinerary": best_itinerary}))
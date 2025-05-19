import itertools
import json

def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {'name': 'Rebecca', 'location': 'Presidio', 'start': time_to_minutes('18:15'), 'end': time_to_minutes('20:45'), 'duration': 60},
    {'name': 'Linda', 'location': 'Sunset District', 'start': time_to_minutes('15:30'), 'end': time_to_minutes('19:45'), 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Haight-Ashbury', 'start': time_to_minutes('17:15'), 'end': time_to_minutes('19:30'), 'duration': 105},
    {'name': 'William', 'location': 'Mission District', 'start': time_to_minutes('13:15'), 'end': time_to_minutes('19:30'), 'duration': 30},
    {'name': 'Robert', 'location': 'Golden Gate Park', 'start': time_to_minutes('14:15'), 'end': time_to_minutes('21:30'), 'duration': 45},
    {'name': 'Mark', 'location': 'Russian Hill', 'start': time_to_minutes('10:00'), 'end': time_to_minutes('21:15'), 'duration': 75}
]

travel_times = {
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Golden Gate Park'): 21
}

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_loc = 'The Castro'
    current_time = 540
    itinerary = []
    met = set()
    
    for friend in perm:
        travel_time = travel_times.get((current_loc, friend['location']), float('inf'))
        arrival = current_time + travel_time
        if arrival > friend['end']:
            continue
        start = max(arrival, friend['start'])
        if start + friend['duration'] > friend['end']:
            continue
        end = start + friend['duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })
        met.add(friend['name'])
        current_time = end
        current_loc = friend['location']
    
    if len(met) > max_met or (len(met) == max_met and current_time < max(current_time for x in best_itinerary if len(best_itinerary))):
        max_met = len(met)
        best_itinerary = itinerary.copy()

output = {
    "itinerary": [
        {
            "action": "meet",
            "location": item['location'],
            "person": item['person'],
            "start_time": item['start_time'],
            "end_time": item['end_time']
        } for item in best_itinerary
    ]
}

print(json.dumps(output, indent=2))
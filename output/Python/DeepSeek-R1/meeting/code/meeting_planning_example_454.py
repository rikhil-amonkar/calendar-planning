import itertools
import json

travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

friends = [
    {'name': 'Jessica', 'location': 'Golden Gate Park', 'start': 13*60+45, 'end':15*60, 'duration':30},
    {'name': 'Ashley', 'location': 'Bayview', 'start':17*60+15, 'end':20*60, 'duration':105},
    {'name': 'Ronald', 'location': 'Chinatown', 'start':7*60+15, 'end':14*60+45, 'duration':90},
    {'name': 'William', 'location': 'North Beach', 'start':13*60+15, 'end':20*60+15, 'duration':15},
    {'name': 'Daniel', 'location': 'Mission District', 'start':7*60, 'end':11*60+15, 'duration':105},
]

def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

best_count = 0
best_time = float('inf')
best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Presidio'
    current_time = 540
    itinerary = []
    met = set()
    
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        travel_time = travel_times.get((from_loc, to_loc))
        if travel_time is None:
            continue
        
        arrival_time = current_time + travel_time
        if arrival_time > friend['end']:
            continue
        
        start_time = max(arrival_time, friend['start'])
        if start_time + friend['duration'] > friend['end']:
            continue
        
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(start_time + friend['duration'])
        })
        met.add(friend['name'])
        current_time = start_time + friend['duration']
        current_location = to_loc
    
    count = len(met)
    if count > best_count or (count == best_count and current_time < best_time):
        best_count = count
        best_time = current_time
        best_itinerary = itinerary.copy()

output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))
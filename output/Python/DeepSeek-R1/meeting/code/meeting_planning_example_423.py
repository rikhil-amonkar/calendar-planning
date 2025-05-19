import itertools
import json

friends = [
    {'name': 'Jason', 'location': 'Richmond District', 'available_start': 780, 'available_end': 1245, 'duration': 90},
    {'name': 'Melissa', 'location': 'North Beach', 'available_start': 1125, 'available_end': 1215, 'duration': 45},
    {'name': 'Brian', 'location': 'Financial District', 'available_start': 585, 'available_end': 1305, 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Golden Gate Park', 'available_start': 525, 'available_end': 1290, 'duration': 105},
    {'name': 'Laura', 'location': 'Union Square', 'available_start': 855, 'available_end': 1170, 'duration': 75}
]

travel_times = {
    ('Presidio', 'Richmond District'):7, ('Presidio', 'North Beach'):18, ('Presidio', 'Financial District'):23,
    ('Presidio', 'Golden Gate Park'):12, ('Presidio', 'Union Square'):22, ('Richmond District', 'Presidio'):7,
    ('Richmond District', 'North Beach'):17, ('Richmond District', 'Financial District'):22, ('Richmond District', 'Golden Gate Park'):9,
    ('Richmond District', 'Union Square'):21, ('North Beach', 'Presidio'):17, ('North Beach', 'Richmond District'):18,
    ('North Beach', 'Financial District'):8, ('North Beach', 'Golden Gate Park'):22, ('North Beach', 'Union Square'):7,
    ('Financial District', 'Presidio'):22, ('Financial District', 'Richmond District'):21, ('Financial District', 'North Beach'):7,
    ('Financial District', 'Golden Gate Park'):23, ('Financial District', 'Union Square'):9, ('Golden Gate Park', 'Presidio'):11,
    ('Golden Gate Park', 'Richmond District'):7, ('Golden Gate Park', 'North Beach'):24, ('Golden Gate Park', 'Financial District'):26,
    ('Golden Gate Park', 'Union Square'):22, ('Union Square', 'Presidio'):24, ('Union Square', 'Richmond District'):20,
    ('Union Square', 'North Beach'):10, ('Union Square', 'Financial District'):9, ('Union Square', 'Golden Gate Park'):22
}

def minutes_to_time(m):
    return f"{m//60}:{m%60:02d}"

best_itinerary = []
best_count = 0
best_end = float('inf')

for perm in itertools.permutations(friends):
    current_time = 540
    current_loc = 'Presidio'
    itinerary = []
    for friend in perm:
        to = friend['location']
        travel = travel_times.get((current_loc, to))
        if not travel:
            continue
        arrive = current_time + travel
        start = max(arrive, friend['available_start'])
        end = start + friend['duration']
        if end > friend['available_end']:
            continue
        itinerary.append({'start': start, 'end': end, 'loc': to, 'name': friend['name']})
        current_time = end
        current_loc = to
    if len(itinerary) > best_count or (len(itinerary) == best_count and current_time < best_end):
        best_count = len(itinerary)
        best_end = current_time
        best_itinerary = itinerary

formatted = []
for meet in best_itinerary:
    formatted.append({
        "action": "meet",
        "location": meet['loc'],
        "person": meet['name'],
        "start_time": minutes_to_time(meet['start']),
        "end_time": minutes_to_time(meet['end'])
    })

print(json.dumps({"itinerary": formatted}, indent=2))
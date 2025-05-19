import itertools
import json

friends = [
    {"name": "Mary", "location": "Golden Gate Park", "start": 8*60+45, "end": 11*60+45, "duration": 45},
    {"name": "Kevin", "location": "Haight-Ashbury", "start": 10*60+15, "end": 16*60+15, "duration": 90},
    {"name": "Deborah", "location": "Bayview", "start": 15*60, "end": 19*60+15, "duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start": 10*60, "end": 17*60+15, "duration": 120},
    {"name": "Emily", "location": "Financial District", "start": 11*60+30, "end": 21*60+45, "duration": 105}
]

travel_times = {
    ('Embarcadero', 'Golden Gate Park'):25, ('Embarcadero', 'Haight-Ashbury'):21, ('Embarcadero', 'Bayview'):21,
    ('Embarcadero', 'Presidio'):20, ('Embarcadero', 'Financial District'):5, ('Golden Gate Park', 'Embarcadero'):25,
    ('Golden Gate Park', 'Haight-Ashbury'):7, ('Golden Gate Park', 'Bayview'):23, ('Golden Gate Park', 'Presidio'):11,
    ('Golden Gate Park', 'Financial District'):26, ('Haight-Ashbury', 'Embarcadero'):20,
    ('Haight-Ashbury', 'Golden Gate Park'):7, ('Haight-Ashbury', 'Bayview'):18, ('Haight-Ashbury', 'Presidio'):15,
    ('Haight-Ashbury', 'Financial District'):21, ('Bayview', 'Embarcadero'):19, ('Bayview', 'Golden Gate Park'):22,
    ('Bayview', 'Haight-Ashbury'):19, ('Bayview', 'Presidio'):31, ('Bayview', 'Financial District'):19,
    ('Presidio', 'Embarcadero'):20, ('Presidio', 'Golden Gate Park'):12, ('Presidio', 'Haight-Ashbury'):15,
    ('Presidio', 'Bayview'):31, ('Presidio', 'Financial District'):23, ('Financial District', 'Embarcadero'):4,
    ('Financial District', 'Golden Gate Park'):23, ('Financial District', 'Haight-Ashbury'):19,
    ('Financial District', 'Bayview'):19, ('Financial District', 'Presidio'):22
}

best = []
max_count = 0
best_end = float('inf')

for size in range(5, 0, -1):
    for perm in itertools.permutations(friends, size):
        time = 9*60
        loc = 'Embarcadero'
        valid = True
        path = []
        
        for p in perm:
            key = (loc, p['location'])
            if key not in travel_times:
                valid = False
                break
            travel = travel_times[key]
            arrive = time + travel
            if arrive > p['end']:
                valid = False
                break
            start = max(arrive, p['start'])
            if start + p['duration'] > p['end']:
                valid = False
                break
            path.append({
                'person': p['name'], 'location': p['location'],
                'start': start, 'end': start + p['duration']
            })
            time = start + p['duration']
            loc = p['location']
        
        if valid:
            if len(perm) > max_count or (len(perm) == max_count and time < best_end):
                max_count = len(perm)
                best = path
                best_end = time
                if max_count == 5:
                    break
    if max_count == 5:
        break

def fmt(t):
    h, m = divmod(t, 60)
    return f"{h}:{m:02d}"

itinerary = []
for meet in best:
    itinerary.append({
        "action": "meet",
        "location": meet['location'],
        "person": meet['person'],
        "start_time": fmt(meet['start']),
        "end_time": fmt(meet['end'])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))
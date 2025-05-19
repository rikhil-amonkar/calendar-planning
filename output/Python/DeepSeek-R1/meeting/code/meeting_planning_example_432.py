import json
from itertools import permutations

def min_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}".replace(":0", ":") if mins < 10 else f"{hours}:{mins}"

travel_times = {
    'Golden Gate Park': {
        "Fisherman's Wharf": 24,
        'Bayview': 23,
        'Mission District': 17,
        'Embarcadero': 25,
        'Financial District': 26
    },
    "Fisherman's Wharf": {
        'Golden Gate Park': 25,
        'Bayview': 26,
        'Mission District': 22,
        'Embarcadero': 8,
        'Financial District': 11
    },
    'Bayview': {
        'Golden Gate Park': 22,
        "Fisherman's Wharf": 25,
        'Mission District': 13,
        'Embarcadero': 19,
        'Financial District': 19
    },
    'Mission District': {
        'Golden Gate Park': 17,
        "Fisherman's Wharf": 22,
        'Bayview': 15,
        'Embarcadero': 19,
        'Financial District': 17
    },
    'Embarcadero': {
        'Golden Gate Park': 25,
        "Fisherman's Wharf": 6,
        'Bayview': 21,
        'Mission District': 20,
        'Financial District': 5
    },
    'Financial District': {
        'Golden Gate Park': 23,
        "Fisherman's Wharf": 10,
        'Bayview': 19,
        'Mission District': 17,
        'Embarcadero': 4
    }
}

friends = [
    {
        'name': 'Joseph',
        'location': "Fisherman's Wharf",
        'start': 8 * 60,
        'end': 17 * 60 + 30,
        'duration': 90
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'start': 11 * 60 + 15,
        'end': 15 * 60 + 15,
        'duration': 30
    },
    {
        'name': 'Barbara',
        'location': 'Financial District',
        'start': 10 * 60 + 30,
        'end': 16 * 60 + 30,
        'duration': 15
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'start': 17 * 60 + 30,
        'end': 21 * 60 + 30,
        'duration': 60
    }
]

best = []
for perm in permutations(friends):
    current_time = 540  # 9:00 AM
    current_loc = 'Golden Gate Park'
    itinerary = []
    valid = True
    
    for f in perm:
        to_loc = f['location']
        tt = travel_times[current_loc].get(to_loc)
        if tt is None:
            valid = False
            break
        arrive = current_time + tt
        if arrive > f['end']:
            valid = False
            break
        
        start = max(arrive, f['start'])
        end = start + f['duration']
        if end > f['end']:
            valid = False
            break
        
        itinerary.append({
            "action": "meet",
            "location": to_loc,
            "person": f['name'],
            "start_time": min_to_time(start),
            "end_time": min_to_time(end)
        })
        current_time = end
        current_loc = to_loc
    
    if valid and len(itinerary) > len(best):
        best = itinerary
        if len(best) == 4:
            break

print(json.dumps({"itinerary": best}, indent=2))
import json
from itertools import permutations

def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

friends = [
    {'name': 'Helen', 'location': 'North Beach', 'start': 7*60, 'end': 16*60+45, 'duration': 120},
    {'name': 'Kimberly', 'location': "Fisherman's Wharf", 'start': 16*60+30, 'end': 21*60, 'duration': 45},
    {'name': 'Patricia', 'location': 'Bayview', 'start': 18*60, 'end': 21*60+15, 'duration': 120}
]

travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', "Fisherman's Wharf"): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', "Fisherman's Wharf"): 5,
    ('North Beach', 'Bayview'): 22,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'North Beach'): 6,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', "Fisherman's Wharf"): 25
}

best = []
max_count = 0

for perm in permutations(friends):
    current_loc = 'Nob Hill'
    current_time = 540
    itinerary = []
    valid = True
    for friend in perm:
        key = (current_loc, friend['location'])
        travel = travel_times.get(key)
        if travel is None:
            valid = False
            break
        arrive = current_time + travel
        start = max(arrive, friend['start'])
        if start + friend['duration'] > friend['end']:
            valid = False
            break
        end = start + friend['duration']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        current_time = end
        current_loc = friend['location']
    if valid and len(perm) > max_count:
        max_count = len(perm)
        best = itinerary
    elif valid and len(perm) == max_count and len(itinerary) > len(best):
        best = itinerary

print(json.dumps({"itinerary": best}, indent=2))
import itertools
import json

friends = [
    {'name': 'Stephanie', 'location': 'Mission District', 'start': 495, 'end': 825, 'duration': 90},
    {'name': 'Sandra', 'location': 'Bayview', 'start': 780, 'end': 1170, 'duration': 15},
    {'name': 'Brian', 'location': 'Russian Hill', 'start': 735, 'end': 960, 'duration': 120},
    {'name': 'Jason', 'location': "Fisherman's Wharf", 'start': 510, 'end': 1065, 'duration': 60}
]

travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Russian Hill'): 7
}

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

best_itinerary = []
best_count = 0
best_end = float('inf')

for perm in itertools.permutations(friends):
    current_time = 540
    current_loc = 'Haight-Ashbury'
    itinerary = []
    count = 0
    valid = True
    for f in perm:
        tt = travel_times.get((current_loc, f['location']), None)
        if tt is None:
            valid = False
            break
        arrive = current_time + tt
        earliest = max(arrive, f['start'])
        latest = f['end'] - f['duration']
        if earliest > latest:
            valid = False
            break
        end = earliest + f['duration']
        itinerary.append({
            'action': 'meet',
            'location': f['location'],
            'person': f['name'],
            'start_time': min_to_time(earliest),
            'end_time': min_to_time(end)
        })
        current_time = end
        current_loc = f['location']
        count += 1
    if valid and (count > best_count or (count == best_count and current_time < best_end)):
        best_count = count
        best_itinerary = itinerary
        best_end = current_time

print(json.dumps({'itinerary': best_itinerary}, separators=(',', ':')))
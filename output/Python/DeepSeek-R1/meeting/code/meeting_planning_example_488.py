import itertools
import json

friends = [
    {'name': 'Ronald', 'location': 'Nob Hill', 'start': 600, 'end': 1020, 'duration': 105},
    {'name': 'Helen', 'location': 'The Castro', 'start': 810, 'end': 1020, 'duration': 120},
    {'name': 'Joshua', 'location': 'Sunset District', 'start': 855, 'end': 1170, 'duration': 90},
    {'name': 'Margaret', 'location': 'Haight-Ashbury', 'start': 615, 'end': 1320, 'duration': 60}
]

travel_time = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'):7,
    ('Pacific Heights', 'The Castro'):16,
    ('Pacific Heights', 'Sunset District'):21,
    ('Pacific Heights', 'Haight-Ashbury'):11,
    ('Nob Hill', 'Pacific Heights'):8,
    ('Nob Hill', 'Russian Hill'):5,
    ('Nob Hill', 'The Castro'):17,
    ('Nob Hill', 'Sunset District'):25,
    ('Nob Hill', 'Haight-Ashbury'):13,
    ('Russian Hill', 'Pacific Heights'):7,
    ('Russian Hill', 'Nob Hill'):5,
    ('Russian Hill', 'The Castro'):21,
    ('Russian Hill', 'Sunset District'):23,
    ('Russian Hill', 'Haight-Ashbury'):17,
    ('The Castro', 'Pacific Heights'):16,
    ('The Castro', 'Nob Hill'):16,
    ('The Castro', 'Russian Hill'):18,
    ('The Castro', 'Sunset District'):17,
    ('The Castro', 'Haight-Ashbury'):6,
    ('Sunset District', 'Pacific Heights'):21,
    ('Sunset District', 'Nob Hill'):27,
    ('Sunset District', 'Russian Hill'):24,
    ('Sunset District', 'The Castro'):17,
    ('Sunset District', 'Haight-Ashbury'):15,
    ('Haight-Ashbury', 'Pacific Heights'):12,
    ('Haight-Ashbury', 'Nob Hill'):15,
    ('Haight-Ashbury', 'Russian Hill'):17,
    ('Haight-Ashbury', 'The Castro'):6,
    ('Haight-Ashbury', 'Sunset District'):15
}

best_count = 0
best_meetings = []
best_end_time = float('inf')

for perm in itertools.permutations(friends):
    current_location = 'Pacific Heights'
    current_time = 540
    meetings = []
    valid = True
    
    for friend in perm:
        to_loc = friend['location']
        tt_key = (current_location, to_loc)
        if tt_key not in travel_time:
            valid = False
            break
        tt = travel_time[tt_key]
        arrival = current_time + tt
        start = max(arrival, friend['start'])
        latest_start = friend['end'] - friend['duration']
        if start > latest_start:
            valid = False
            break
        end = start + friend['duration']
        if end > friend['end']:
            valid = False
            break
        meetings.append({'friend': friend, 'start': start, 'end': end, 'location': to_loc})
        current_time = end
        current_location = to_loc
    
    if valid:
        count = len(meetings)
        if count > best_count or (count == best_count and current_time < best_end_time):
            best_count = count
            best_meetings = meetings
            best_end_time = current_time

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

itinerary = []
for meet in best_meetings:
    itinerary.append({
        "action": "meet",
        "location": meet['location'],
        "person": meet['friend']['name'],
        "start_time": min_to_time(meet['start']),
        "end_time": min_to_time(meet['end'])
    })

print(json.dumps({"itinerary": itinerary}))
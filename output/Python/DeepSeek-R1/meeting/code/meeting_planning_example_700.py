import itertools
import json

friends = [
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'start': 20 * 60,
        'end': 21 * 60,
        'duration': 15
    },
    {
        'name': 'Emily',
        'location': 'Fisherman\'s Wharf',
        'start': 16 * 60 + 15,
        'end': 19 * 60,
        'duration': 30
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'start': 18 * 60 + 15,
        'end': 19 * 60 + 45,
        'duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'start': 17 * 60,
        'end': 19 * 60,
        'duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Sunset District',
        'start': 19 * 60,
        'end': 21 * 60 + 15,
        'duration': 75
    },
    {
        'name': 'Mary',
        'location': 'Nob Hill',
        'start': 17 * 60 + 30,
        'end': 19 * 60,
        'duration': 45
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'start': 11 * 60,
        'end': 12 * 60 + 15,
        'duration': 45
    },
]

travel_time = {
    'Presidio': {'Pacific Heights': 11, 'Golden Gate Park': 12, 'Fisherman\'s Wharf': 19, 'Marina District': 11, 'Alamo Square': 19, 'Sunset District': 15, 'Nob Hill': 18, 'North Beach': 18},
    'Pacific Heights': {'Presidio': 11, 'Golden Gate Park': 15, 'Fisherman\'s Wharf': 13, 'Marina District': 6, 'Alamo Square': 10, 'Sunset District': 21, 'Nob Hill': 8, 'North Beach': 9},
    'Golden Gate Park': {'Presidio': 11, 'Pacific Heights': 16, 'Fisherman\'s Wharf': 24, 'Marina District': 16, 'Alamo Square': 9, 'Sunset District': 10, 'Nob Hill': 20, 'North Beach': 23},
    'Fisherman\'s Wharf': {'Presidio': 17, 'Pacific Heights': 12, 'Golden Gate Park': 25, 'Marina District': 9, 'Alamo Square': 21, 'Sunset District': 27, 'Nob Hill': 11, 'North Beach': 6},
    'Marina District': {'Presidio': 10, 'Pacific Heights': 7, 'Golden Gate Park': 18, 'Fisherman\'s Wharf': 10, 'Alamo Square': 15, 'Sunset District': 19, 'Nob Hill': 12, 'North Beach': 11},
    'Alamo Square': {'Presidio': 17, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Fisherman\'s Wharf': 19, 'Marina District': 15, 'Sunset District': 16, 'Nob Hill': 11, 'North Beach': 15},
    'Sunset District': {'Presidio': 16, 'Pacific Heights': 21, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 29, 'Marina District': 21, 'Alamo Square': 17, 'Nob Hill': 27, 'North Beach': 28},
    'Nob Hill': {'Presidio': 17, 'Pacific Heights': 8, 'Golden Gate Park': 17, 'Fisherman\'s Wharf': 10, 'Marina District': 11, 'Alamo Square': 11, 'Sunset District': 24, 'North Beach': 8},
    'North Beach': {'Presidio': 17, 'Pacific Heights': 8, 'Golden Gate Park': 22, 'Fisherman\'s Wharf': 5, 'Marina District': 9, 'Alamo Square': 16, 'Sunset District': 27, 'Nob Hill': 7},
}

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}".lstrip('0') if hours != 0 else f"{hours}:{minutes:02d}"

best_count = 0
best_duration = 0
best_itinerary = []

for perm in itertools.permutations(friends):
    current_loc = 'Presidio'
    current_time = 9 * 60
    itinerary = []
    total_dur = 0
    count = 0
    valid = True
    for f in perm:
        try:
            tt = travel_time[current_loc][f['location']]
        except KeyError:
            valid = False
            break
        arrival = current_time + tt
        start = max(arrival, f['start'])
        end = start + f['duration']
        if end > f['end'] or start > f['end']:
            valid = False
            break
        itinerary.append((f, start, end))
        current_time = end
        current_loc = f['location']
        total_dur += f['duration']
        count += 1
    if valid and (count > best_count or (count == best_count and total_dur > best_duration)):
        best_count = count
        best_duration = total_dur
        best_itinerary = itinerary

output = {"itinerary": []}
for entry in best_itinerary:
    f, start, end = entry
    output["itinerary"].append({
        "action": "meet",
        "location": f['location'],
        "person": f['name'],
        "start_time": minutes_to_time(start).replace(':00', ':0') if minutes_to_time(start).endswith(':00') else minutes_to_time(start),
        "end_time": minutes_to_time(end).replace(':00', ':0') if minutes_to_time(end).endswith(':00') else minutes_to_time(end)
    })

print(json.dumps(output, indent=2))
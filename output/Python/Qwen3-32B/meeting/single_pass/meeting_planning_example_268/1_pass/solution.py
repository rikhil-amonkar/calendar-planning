import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
}

friends = [
    {
        'name': 'Timothy',
        'location': 'Alamo Square',
        'available_start': 720,  # 12:00 PM
        'available_end': 975,    # 4:15 PM
        'min_duration': 105
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'available_start': 1125, # 6:45 PM
        'available_end': 1260,   # 9:00 PM
        'min_duration': 60
    },
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'available_start': 1005, # 4:45 PM
        'available_end': 1290,   # 9:30 PM
        'min_duration': 60
    }
]

valid_itineraries = []

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Golden Gate Park'
    itinerary = []
    valid = True
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        if (from_loc, to_loc) not in travel_times:
            valid = False
            break
        travel_time = travel_times[(from_loc, to_loc)]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['available_start'])
        meeting_end = meeting_start + friend['min_duration']
        if meeting_end > friend['available_end']:
            valid = False
            break
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_end)
        })
        current_time = meeting_end
        current_location = to_loc
    if valid:
        valid_itineraries.append( (current_time, itinerary) )

if valid_itineraries:
    valid_itineraries.sort()
    best_itinerary = valid_itineraries[0][1]
    print(json.dumps({"itinerary": best_itinerary}))
else:
    print(json.dumps({"itinerary": []}))
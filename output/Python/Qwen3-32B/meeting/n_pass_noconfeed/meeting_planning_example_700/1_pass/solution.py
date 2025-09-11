import itertools
import json

# Define friends (excluding Kevin)
friends = [
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'available_start': 20 * 60,  # 8 PM
        'available_end': 21 * 60,    # 9 PM
        'min_duration': 15
    },
    {
        'name': 'Emily',
        'location': "Fisherman's Wharf",
        'available_start': 16 * 60 + 15,  # 4:15 PM
        'available_end': 19 * 60,         # 7:00 PM
        'min_duration': 30
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': 18 * 60 + 15,  # 6:15 PM
        'available_end': 19 * 60 + 45,    # 7:45 PM
        'min_duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': 17 * 60,       # 5:00 PM
        'available_end': 19 * 60,         # 7:00 PM
        'min_duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Sunset District',
        'available_start': 19 * 60,       # 7:00 PM
        'available_end': 21 * 60 + 15,    # 9:15 PM
        'min_duration': 75
    },
    {
        'name': 'Mary',
        'location': 'Nob Hill',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 19 * 60,         # 7:00 PM
        'min_duration': 45
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': 11 * 60,       # 11:00 AM
        'available_end': 12 * 60 + 15,    # 12:15 PM
        'min_duration': 45
    }
]

# Define travel times between locations
travel_time = {
    'Presidio': {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18
    },
    "Pacific Heights": {
        'Presidio': 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9
    },
    "Golden Gate Park": {
        'Presidio': 12,
        "Pacific Heights": 15,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23
    },
    "Fisherman's Wharf": {
        'Presidio': 19,
        "Pacific Heights": 13,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6
    },
    "Marina District": {
        'Presidio': 11,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11
    },
    "Alamo Square": {
        'Presidio': 19,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 21,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "Sunset District": {
        'Presidio': 15,
        "Pacific Heights": 21,
        "Golden Gate Park": 10,
        "Fisherman's Wharf": 27,
        "Marina District": 19,
        "Alamo Square": 16,
        "Nob Hill": 27,
        "North Beach": 28
    },
    "Nob Hill": {
        'Presidio': 18,
        "Pacific Heights": 8,
        "Golden Gate Park": 20,
        "Fisherman's Wharf": 11,
        "Marina District": 12,
        "Alamo Square": 11,
        "Sunset District": 27,
        "North Beach": 8
    },
    "North Beach": {
        'Presidio': 18,
        "Pacific Heights": 9,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 6,
        "Marina District": 11,
        "Alamo Square": 15,
        "Sunset District": 28,
        "Nob Hill": 7
    }
}

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def simulate_schedule(perm):
    current_time = 9 * 60  # 9:00 AM
    current_location = 'Presidio'
    itinerary = []
    for friend in perm:
        travel_duration = travel_time[current_location][friend['location']]
        arrival_time = current_time + travel_duration
        start_time = max(arrival_time, friend['available_start'])
        meeting_end_time = start_time + friend['min_duration']
        
        if meeting_end_time > friend['available_end']:
            return None
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(meeting_end_time)
        })
        
        current_time = meeting_end_time
        current_location = friend['location']
    return itinerary

best_itinerary = None
best_count = 0

for perm in itertools.permutations(friends):
    itinerary = simulate_schedule(perm)
    if itinerary is not None:
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary

result = {
    "itinerary": best_itinerary or []
}

print(json.dumps(result, indent=2))
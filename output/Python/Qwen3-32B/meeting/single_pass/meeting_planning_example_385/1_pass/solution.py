import itertools
import json

def time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Jeffrey',
        'location': 'Presidio',
        'available_start': 8 * 60,  # 8:00 AM
        'available_end': 10 * 60,   # 10:00 AM
        'required_duration': 105
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': 13 * 60 + 30,  # 1:30 PM
        'available_end': 22 * 60,         # 10:00 PM
        'required_duration': 45
    },
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': 18 * 60,       # 6:00 PM
        'available_end': 21 * 60 + 30,    # 9:30 PM
        'required_duration': 30
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': 9 * 60,        # 9:00 AM
        'available_end': 13 * 60 + 30,    # 1:30 PM
        'required_duration': 15
    }
]

travel_times = {
    'Nob Hill': {
        'Presidio': 17,
        'North Beach': 8,
        "Fisherman's Wharf": 11,
        'Pacific Heights': 8
    },
    'Presidio': {
        'Nob Hill': 18,
        'North Beach': 18,
        "Fisherman's Wharf": 19,
        'Pacific Heights': 11
    },
    'North Beach': {
        'Nob Hill': 7,
        'Presidio': 17,
        "Fisherman's Wharf": 5,
        'Pacific Heights': 8
    },
    "Fisherman's Wharf": {
        'Nob Hill': 11,
        'Presidio': 17,
        'North Beach': 6,
        'Pacific Heights': 12
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Presidio': 11,
        'North Beach': 9,
        "Fisherman's Wharf": 13
    }
}

best_itinerary = []
max_friends = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM
    current_location = 'Nob Hill'
    itinerary = []
    for friend in perm:
        next_location = friend['location']
        travel_time = travel_times.get(current_location, {}).get(next_location, None)
        if travel_time is None:
            break  # Can't reach this location, skip this permutation
        arrival_time = current_time + travel_time
        if arrival_time > friend['available_end']:
            break
        start_meeting = max(arrival_time, friend['available_start'])
        end_meeting = start_meeting + friend['required_duration']
        if end_meeting > friend['available_end']:
            break
        itinerary.append({
            'action': 'meet',
            'location': next_location,
            'person': friend['name'],
            'start_time': time_str(start_meeting),
            'end_time': time_str(end_meeting)
        })
        current_time = end_meeting
        current_location = next_location
    else:
        if len(itinerary) > max_friends:
            max_friends = len(itinerary)
            best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
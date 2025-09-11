import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Daniel',
        'location': 'Mission District',
        'start_time': 420,  # 7:00 AM
        'end_time': 675,    # 11:15 AM
        'min_duration': 105
    },
    {
        'name': 'Ronald',
        'location': 'Chinatown',
        'start_time': 435,  # 7:15 AM
        'end_time': 885,    # 2:45 PM
        'min_duration': 90
    },
    {
        'name': 'William',
        'location': 'North Beach',
        'start_time': 795,  # 1:15 PM
        'end_time': 1215,   # 8:15 PM
        'min_duration': 15
    },
    {
        'name': 'Jessica',
        'location': 'Golden Gate Park',
        'start_time': 825,  # 1:45 PM
        'end_time': 900,    # 3:00 PM
        'min_duration': 30
    },
    {
        'name': 'Ashley',
        'location': 'Bayview',
        'start_time': 1035, # 5:15 PM
        'end_time': 1200,   # 8:00 PM
        'min_duration': 105
    }
]

travel_time = {
    'Presidio': {
        'Golden Gate Park': 12,
        'Bayview': 31,
        'Chinatown': 21,
        'North Beach': 18,
        'Mission District': 26,
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Bayview': 23,
        'Chinatown': 23,
        'North Beach': 24,
        'Mission District': 17,
    },
    'Bayview': {
        'Presidio': 31,
        'Golden Gate Park': 22,
        'Chinatown': 18,
        'North Beach': 21,
        'Mission District': 13,
    },
    'Chinatown': {
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 22,
        'North Beach': 3,
        'Mission District': 18,
    },
    'North Beach': {
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 22,
        'Chinatown': 6,
        'Mission District': 18,
    },
    'Mission District': {
        'Presidio': 25,
        'Golden Gate Park': 17,
        'Bayview': 15,
        'Chinatown': 16,
        'North Beach': 17,
    },
}

def is_feasible(perm):
    current_time = 540  # 9:00 AM
    current_location = 'Presidio'
    for friend in perm:
        travel_time_minutes = travel_time[current_location][friend['location']]
        arrival_time = current_time + travel_time_minutes
        friend_start = friend['start_time']
        friend_end = friend['end_time']
        required = friend['min_duration']
        earliest_start = max(arrival_time, friend_start)
        if earliest_start + required > friend_end:
            return False
        current_time = earliest_start + required
        current_location = friend['location']
    return True

def generate_itinerary(perm):
    current_time = 540
    current_location = 'Presidio'
    itinerary = []
    for friend in perm:
        travel_time_minutes = travel_time[current_location][friend['location']]
        arrival_time = current_time + travel_time_minutes
        friend_start = friend['start_time']
        friend_end = friend['end_time']
        required = friend['min_duration']
        earliest_start = max(arrival_time, friend_start)
        end_time = earliest_start + required
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(earliest_start),
            'end_time': format_time(end_time)
        })
        current_time = end_time
        current_location = friend['location']
    return itinerary

for subset_size in range(5, 0, -1):
    for perm in itertools.permutations(friends, subset_size):
        if is_feasible(perm):
            result = {"itinerary": generate_itinerary(perm)}
            print(json.dumps(result))
            exit()
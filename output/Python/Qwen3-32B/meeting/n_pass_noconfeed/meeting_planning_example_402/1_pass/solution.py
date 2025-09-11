import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

friends = [
    {
        'name': 'Matthew',
        'location': 'Marina District',
        'available_start': '9:15',
        'available_end': '12:00',
        'required_duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Union Square',
        'available_start': '10:15',
        'available_end': '21:45',
        'required_duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'available_start': '14:15',
        'available_end': '18:45',
        'required_duration': 30
    },
    {
        'name': 'Patricia',
        'location': 'Sunset District',
        'available_start': '17:00',
        'available_end': '19:45',
        'required_duration': 45
    },
    {
        'name': 'Sarah',
        'location': 'Haight-Ashbury',
        'available_start': '17:00',
        'available_end': '21:30',
        'required_duration': 105
    }
]

travel_times = {
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Sunset District': 10,
        'Marina District': 16,
        'Financial District': 26,
        'Union Square': 22
    },
    'Haight-Ashbury': {
        'Golden Gate Park': 7,
        'Sunset District': 15,
        'Marina District': 17,
        'Financial District': 21,
        'Union Square': 17
    },
    'Sunset District': {
        'Golden Gate Park': 11,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Financial District': 30,
        'Union Square': 30
    },
    'Marina District': {
        'Golden Gate Park': 18,
        'Haight-Ashbury': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Union Square': 16
    },
    'Financial District': {
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Sunset District': 31,
        'Marina District': 15,
        'Union Square': 9
    },
    'Union Square': {
        'Golden Gate Park': 22,
        'Haight-Ashbury': 18,
        'Sunset District': 26,
        'Marina District': 18,
        'Financial District': 9
    }
}

best_itinerary = []
best_length = 0

for perm in itertools.permutations(friends):
    current_location = 'Golden Gate Park'
    current_time = time_str_to_minutes('9:00')  # Start at 9:00 AM
    itinerary = []
    feasible = True

    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time

        friend_start = time_str_to_minutes(friend['available_start'])
        friend_end = time_str_to_minutes(friend['available_end'])
        required_duration = friend['required_duration']

        earliest_start = max(arrival_time, friend_start)

        if earliest_start + required_duration > friend_end:
            feasible = False
            break

        start_time_str = minutes_to_time_str(earliest_start)
        end_time_str = minutes_to_time_str(earliest_start + required_duration)
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_time_str,
            'end_time': end_time_str
        })

        current_time = earliest_start + required_duration
        current_location = friend['location']

    if feasible and len(itinerary) > best_length:
        best_length = len(itinerary)
        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
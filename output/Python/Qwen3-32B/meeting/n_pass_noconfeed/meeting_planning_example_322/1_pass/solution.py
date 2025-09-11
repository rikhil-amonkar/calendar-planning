import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times between locations
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'Chinatown': 30,
        'Presidio': 16,
        'Fisherman\'s Wharf': 29
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Fisherman\'s Wharf': 7
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'Presidio': 19,
        'Fisherman\'s Wharf': 8
    },
    'Presidio': {
        'Sunset District': 15,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Fisherman\'s Wharf': 19
    },
    'Fisherman\'s Wharf': {
        'Sunset District': 27,
        'Russian Hill': 7,
        'Chinatown': 12,
        'Presidio': 17
    }
}

# Friends' data
friends_data = [
    {
        'name': 'William',
        'location': 'Russian Hill',
        'available_start': '18:30',
        'available_end': '20:45',
        'min_duration': 105
    },
    {
        'name': 'Michelle',
        'location': 'Chinatown',
        'available_start': '8:15',
        'available_end': '14:00',
        'min_duration': 15
    },
    {
        'name': 'George',
        'location': 'Presidio',
        'available_start': '10:30',
        'available_end': '18:45',
        'min_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:00',
        'available_end': '13:45',
        'min_duration': 30
    }
]

# Convert friends' available times to minutes
for f in friends_data:
    f['available_start_minutes'] = time_str_to_minutes(f['available_start'])
    f['available_end_minutes'] = time_str_to_minutes(f['available_end'])

friends_names = [f['name'] for f in friends_data]

# Starting conditions
start_location = 'Sunset District'
start_time_minutes = time_str_to_minutes('9:00')

best_schedule = None
best_count = 0

for perm in itertools.permutations(friends_names):
    current_location = start_location
    current_time = start_time_minutes
    schedule = []
    valid = True
    friends_met = 0

    for name in perm:
        friend = next(f for f in friends_data if f['name'] == name)
        location = friend['location']
        available_start = friend['available_start_minutes']
        available_end = friend['available_end_minutes']
        min_duration = friend['min_duration']

        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time

        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration

        if end_time > available_end:
            valid = False
            break

        schedule.append({
            'action': 'meet',
            'location': location,
            'person': name,
            'start_time': start_time,
            'end_time': end_time
        })

        current_time = end_time
        current_location = location
        friends_met += 1

    if valid and friends_met > best_count:
        best_count = friends_met
        best_schedule = schedule

if best_schedule:
    itinerary = []
    for entry in best_schedule:
        itinerary.append({
            'action': 'meet',
            'location': entry['location'],
            'person': entry['person'],
            'start_time': minutes_to_time_str(entry['start_time']),
            'end_time': minutes_to_time_str(entry['end_time'])
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid schedule found"}))
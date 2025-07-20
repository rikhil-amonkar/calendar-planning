import itertools
import json

def time_str_to_minutes(time_str):
    time_str = time_str.strip().upper()
    if time_str.endswith('AM') or time_str.endswith('PM'):
        suffix = time_str[-2:]
        time_part = time_str[:-2].strip()
        parts = time_part.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        if suffix == 'AM':
            if hour == 12:
                hour = 0
            return hour * 60 + minute
        else:
            if hour != 12:
                hour += 12
            return hour * 60 + minute
    else:
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

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

friends_info = [
    {
        'name': 'Jeffrey',
        'location': 'Presidio',
        'available_start': '8:00AM',
        'available_end': '10:00AM',
        'min_duration': 105
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': '9:00AM',
        'available_end': '1:30PM',
        'min_duration': 15
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': '1:30PM',
        'available_end': '10:00PM',
        'min_duration': 45
    },
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': '6:00PM',
        'available_end': '9:30PM',
        'min_duration': 30
    }
]

friends = []
for friend in friends_info:
    start_minutes = time_str_to_minutes(friend['available_start'])
    end_minutes = time_str_to_minutes(friend['available_end'])
    friends.append({
        'name': friend['name'],
        'location': friend['location'],
        'available_start_minutes': start_minutes,
        'available_end_minutes': end_minutes,
        'min_duration': friend['min_duration']
    })

start_location = 'Nob Hill'
start_time_minutes = time_str_to_minutes('9:00AM')

best_count = -1
best_itinerary = None

for perm in itertools.permutations(friends):
    current_location = start_location
    current_time = start_time_minutes
    itinerary_current = []
    count = 0
    for friend in perm:
        try:
            travel_time = travel_times[current_location][friend['location']]
        except KeyError:
            continue
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['available_start_minutes'])
        meeting_end = meeting_start + friend['min_duration']
        if meeting_end > friend['available_end_minutes']:
            continue
        count += 1
        itinerary_current.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        current_location = friend['location']
        current_time = meeting_end
    if count > best_count:
        best_count = count
        best_itinerary = itinerary_current

output = {"itinerary": best_itinerary} if best_itinerary is not None else {"itinerary": []}
print(json.dumps(output))
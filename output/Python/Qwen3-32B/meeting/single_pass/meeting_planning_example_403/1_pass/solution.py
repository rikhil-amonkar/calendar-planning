import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

friends = [
    {
        'name': 'Andrew',
        'location': 'Golden Gate Park',
        'available_start': '11:45',
        'available_end': '14:30',
        'min_duration': 75
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'available_start': '16:15',
        'available_end': '18:45',
        'min_duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'available_start': '17:30',
        'available_end': '19:15',
        'min_duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Chinatown',
        'available_start': '9:45',
        'available_end': '21:30',
        'min_duration': 90
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'available_start': '8:30',
        'available_end': '14:15',
        'min_duration': 30
    }
]

travel_times = {
    'Union Square': {
        'Union Square': 0,
        'Golden Gate Park': 22,
        'Pacific Heights': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'The Castro': 19
    },
    'Golden Gate Park': {
        'Union Square': 22,
        'Golden Gate Park': 0,
        'Pacific Heights': 16,
        'Presidio': 11,
        'Chinatown': 23,
        'The Castro': 13
    },
    'Pacific Heights': {
        'Union Square': 15,
        'Golden Gate Park': 16,
        'Pacific Heights': 0,
        'Presidio': 11,
        'Chinatown': 11,
        'The Castro': 16
    },
    'Presidio': {
        'Union Square': 24,
        'Golden Gate Park': 11,
        'Pacific Heights': 11,
        'Presidio': 0,
        'Chinatown': 21,
        'The Castro': 21
    },
    'Chinatown': {
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Pacific Heights': 10,
        'Presidio': 19,
        'Chinatown': 0,
        'The Castro': 22
    },
    'The Castro': {
        'Union Square': 19,
        'Golden Gate Park': 13,
        'Pacific Heights': 16,
        'Presidio': 20,
        'Chinatown': 20,
        'The Castro': 0
    }
}

def is_valid_sequence(sequence):
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    for friend in sequence:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        avail_start = time_to_minutes(friend['available_start'])
        avail_end = time_to_minutes(friend['available_end'])
        if arrival_time > avail_end:
            return False
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + friend['min_duration']
        if meeting_end > avail_end:
            return False
        current_time = meeting_end
        current_location = friend['location']
    return True

best_sequence = None

for k in range(len(friends), 0, -1):
    for combo in itertools.combinations(friends, k):
        for perm in itertools.permutations(combo):
            if is_valid_sequence(perm):
                best_sequence = perm
                break
        if best_sequence is not None:
            break
    if best_sequence is not None:
        break

itinerary = []
if best_sequence:
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    for friend in best_sequence:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        avail_start = time_to_minutes(friend['available_start'])
        avail_end = time_to_minutes(friend['available_end'])
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + friend['min_duration']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
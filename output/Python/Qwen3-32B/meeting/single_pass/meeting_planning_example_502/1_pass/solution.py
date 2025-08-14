import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

friends = [
    {
        'name': 'Stephanie',
        'location': 'Golden Gate Park',
        'available_start': time_str_to_minutes('11:00'),
        'available_end': time_str_to_minutes('15:00'),
        'required_duration': 105,
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'available_start': time_str_to_minutes('13:45'),
        'available_end': time_str_to_minutes('16:30'),
        'required_duration': 15,
    },
    {
        'name': 'Brian',
        'location': 'Union Square',
        'available_start': time_str_to_minutes('15:00'),
        'available_end': time_str_to_minutes('17:15'),
        'required_duration': 30,
    },
    {
        'name': 'Rebecca',
        'location': "Fisherman's Wharf",
        'available_start': time_str_to_minutes('8:00'),
        'available_end': time_str_to_minutes('11:15'),
        'required_duration': 30,
    },
    {
        'name': 'Joseph',
        'location': 'Pacific Heights',
        'available_start': time_str_to_minutes('8:15'),
        'available_end': time_str_to_minutes('9:30'),
        'required_duration': 60,
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': time_str_to_minutes('14:30'),
        'available_end': time_str_to_minutes('20:45'),
        'required_duration': 120,
    },
]

travel_times = {
    'Financial District': {
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Union Square': 9,
        "Fisherman's Wharf": 10,
        'Pacific Heights': 13,
        'North Beach': 7,
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Chinatown': 23,
        'Union Square': 22,
        "Fisherman's Wharf": 24,
        'Pacific Heights': 16,
        'North Beach': 24,
    },
    'Chinatown': {
        'Financial District': 5,
        'Golden Gate Park': 23,
        'Union Square': 7,
        "Fisherman's Wharf": 8,
        'Pacific Heights': 10,
        'North Beach': 3,
    },
    'Union Square': {
        'Financial District': 9,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        "Fisherman's Wharf": 15,
        'Pacific Heights': 15,
        'North Beach': 10,
    },
    "Fisherman's Wharf": {
        'Financial District': 11,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Union Square': 13,
        'Pacific Heights': 12,
        'North Beach': 6,
    },
    'Pacific Heights': {
        'Financial District': 13,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Union Square': 12,
        "Fisherman's Wharf": 13,
        'North Beach': 9,
    },
    'North Beach': {
        'Financial District': 8,
        'Golden Gate Park': 22,
        'Chinatown': 6,
        'Union Square': 7,
        "Fisherman's Wharf": 5,
        'Pacific Heights': 8,
    },
}

best_sequence = []
best_count = 0

for k in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, k):
        for perm in itertools.permutations(subset):
            current_time = 9 * 60  # 9:00 AM in minutes
            current_location = 'Financial District'
            valid = True
            for friend in perm:
                try:
                    travel_time = travel_times[current_location][friend['location']]
                except KeyError:
                    valid = False
                    break
                arrival_time = current_time + travel_time
                available_start = friend['available_start']
                available_end = friend['available_end']
                required = friend['required_duration']
                earliest_start = max(arrival_time, available_start)
                latest_start = available_end - required
                if earliest_start > latest_start:
                    valid = False
                    break
                current_time = earliest_start + required
                current_location = friend['location']
            if valid:
                best_sequence = perm
                best_count = k
                break
        if 'best_sequence' in locals() and len(best_sequence) > 0:
            break
    if 'best_sequence' in locals() and len(best_sequence) > 0:
        break

# Generate the itinerary
itinerary = []
current_time = 9 * 60
current_location = 'Financial District'
for friend in best_sequence:
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    available_start = friend['available_start']
    available_end = friend['available_end']
    required = friend['required_duration']
    earliest_start = max(arrival_time, available_start)
    meeting_start = earliest_start
    meeting_end = meeting_start + required
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time_str(meeting_start),
        'end_time': minutes_to_time_str(meeting_end)
    })
    current_time = meeting_end
    current_location = friend['location']

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
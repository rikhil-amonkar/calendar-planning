import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {'name': 'Nancy', 'location': 'Presidio', 'available_start': 705, 'available_end': 1200, 'required': 30},
    {'name': 'Matthew', 'location': 'Russian Hill', 'available_start': 945, 'available_end': 1305, 'required': 75},
    {'name': 'Karen', 'location': 'The Castro', 'available_start': 1020, 'available_end': 1260, 'required': 45},
    {'name': 'Paul', 'location': 'Nob Hill', 'available_start': 975, 'available_end': 1230, 'required': 60},
    {'name': 'Carol', 'location': 'Union Square', 'available_start': 1080, 'available_end': 1215, 'required': 120},
    {'name': 'Patricia', 'location': 'Chinatown', 'available_start': 1200, 'available_end': 1290, 'required': 75},
    {'name': 'Jeffrey', 'location': 'Pacific Heights', 'available_start': 1200, 'available_end': 1245, 'required': 45},
]

travel_times = {
    'Bayview': {
        'Nob Hill': 20,
        'Union Square': 17,
        'Chinatown': 18,
        'The Castro': 20,
        'Presidio': 31,
        'Pacific Heights': 23,
        'Russian Hill': 23,
    },
    'Nob Hill': {
        'Bayview': 19,
        'Union Square': 7,
        'Chinatown': 6,
        'The Castro': 17,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Russian Hill': 5,
    },
    'Union Square': {
        'Bayview': 15,
        'Nob Hill': 9,
        'Chinatown': 7,
        'The Castro': 19,
        'Presidio': 24,
        'Pacific Heights': 15,
        'Russian Hill': 13,
    },
    'Chinatown': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 7,
        'The Castro': 22,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Russian Hill': 7,
    },
    'The Castro': {
        'Bayview': 19,
        'Nob Hill': 16,
        'Union Square': 19,
        'Chinatown': 20,
        'Presidio': 20,
        'Pacific Heights': 16,
        'Russian Hill': 18,
    },
    'Presidio': {
        'Bayview': 31,
        'Nob Hill': 18,
        'Union Square': 22,
        'Chinatown': 21,
        'The Castro': 21,
        'Pacific Heights': 11,
        'Russian Hill': 14,
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 12,
        'Chinatown': 11,
        'The Castro': 16,
        'Presidio': 11,
        'Russian Hill': 7,
    },
    'Russian Hill': {
        'Bayview': 23,
        'Nob Hill': 5,
        'Union Square': 11,
        'Chinatown': 9,
        'The Castro': 21,
        'Presidio': 14,
        'Pacific Heights': 7,
    },
}

best_itinerary = []
best_length = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Bayview'
    itinerary = []
    for friend in perm:
        to_loc = friend['location']
        travel_time = travel_times[current_location][to_loc]
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required']
        latest_start = available_end - required
        earliest_start = max(arrival_time, available_start)
        if earliest_start > latest_start:
            break  # can't meet this friend
        # schedule the meeting
        start_time = earliest_start
        end_time = start_time + required
        itinerary.append( (friend['name'], to_loc, start_time, end_time) )
        current_time = end_time
        current_location = to_loc
    # update best itinerary
    if len(itinerary) > best_length:
        best_length = len(itinerary)
        best_itinerary = itinerary
    elif len(itinerary) == best_length and best_length != 0:
        # compare end times to choose the one that ends earlier
        if best_itinerary:
            current_best_end = best_itinerary[-1][2] if best_itinerary else 0
            candidate_end = itinerary[-1][2] if itinerary else 0
            if candidate_end < current_best_end:
                best_itinerary = itinerary

# Convert best_itinerary to JSON format
json_itinerary = []
for entry in best_itinerary:
    name, location, start, end = entry
    json_itinerary.append({
        "action": "meet",
        "location": location,
        "person": name,
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })

result = {"itinerary": json_itinerary}

print(json.dumps(result, indent=2))
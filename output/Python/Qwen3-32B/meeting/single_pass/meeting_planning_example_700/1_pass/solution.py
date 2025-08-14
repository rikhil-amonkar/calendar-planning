import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations
travel_times = {
    'Presidio': {
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
        'Alamo Square': 19,
        'Sunset District': 15,
        'Nob Hill': 18,
        'North Beach': 18
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Alamo Square': 10,
        'Sunset District': 21,
        'Nob Hill': 8,
        'North Beach': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Pacific Heights': 16,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Alamo Square': 9,
        'Sunset District': 10,
        'Nob Hill': 20,
        'North Beach': 23
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
        'Marina District': 9,
        'Alamo Square': 21,
        'Sunset District': 27,
        'Nob Hill': 11,
        'North Beach': 5
    },
    'Marina District': {
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Fisherman\'s Wharf': 9,
        'Alamo Square': 15,
        'Sunset District': 19,
        'Nob Hill': 12,
        'North Beach': 9
    },
    'Alamo Square': {
        'Presidio': 17,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
        'Sunset District': 16,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'Sunset District': {
        'Presidio': 16,
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'Fisherman\'s Wharf': 27,
        'Marina District': 19,
        'Alamo Square': 17,
        'Nob Hill': 27,
        'North Beach': 28
    },
    'Nob Hill': {
        'Presidio': 17,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 10,
        'Marina District': 11,
        'Alamo Square': 11,
        'Sunset District': 27,
        'North Beach': 7
    },
    'North Beach': {
        'Presidio': 17,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
        'Alamo Square': 16,
        'Sunset District': 27,
        'Nob Hill': 7
    }
}

# Define friends' meeting constraints
friends = [
    {'name': 'Helen', 'location': 'North Beach', 'available_start': 660, 'available_end': 735, 'required': 45},
    {'name': 'Barbara', 'location': 'Alamo Square', 'available_start': 1020, 'available_end': 1140, 'required': 120},
    {'name': 'Mary', 'location': 'Nob Hill', 'available_start': 1050, 'available_end': 1140, 'required': 45},
    {'name': 'Emily', 'location': 'Fisherman\'s Wharf', 'available_start': 975, 'available_end': 1140, 'required': 30},
    {'name': 'Mark', 'location': 'Marina District', 'available_start': 1095, 'available_end': 1185, 'required': 75},
    {'name': 'Laura', 'location': 'Sunset District', 'available_start': 1140, 'available_end': 1275, 'required': 75},
    {'name': 'Michelle', 'location': 'Golden Gate Park', 'available_start': 1200, 'available_end': 1260, 'required': 15}
]

best_itinerary = []
max_length = 0

# Try all permutations of friends to find the best itinerary
for r in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 540  # 9:00 AM in minutes
        current_location = 'Presidio'
        valid = True
        itinerary = []
        for friend in perm:
            dest = friend['location']
            travel_time = travel_times[current_location][dest]
            arrival_time = current_time + travel_time
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required']
            start_time = max(arrival_time, available_start)
            end_time = start_time + required
            if end_time > available_end:
                valid = False
                break
            current_time = end_time
            current_location = dest
            itinerary.append({
                'action': 'meet',
                'location': dest,
                'person': friend['name'],
                'start_time': minutes_to_time_str(start_time),
                'end_time': minutes_to_time_str(end_time)
            })
        if valid and len(itinerary) > max_length:
            max_length = len(itinerary)
            best_itinerary = itinerary
            if max_length == len(friends):
                break
    if max_length == len(friends):
        break

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
import itertools
import json

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def is_feasible(perm, travel_times):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Golden Gate Park'
    for friend in perm:
        # Get the travel time from current_location to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Determine the start time of the meeting
        start = max(arrival_time, friend['start'])
        end = start + friend['required']
        if end > friend['end']:
            return False
        # Update current time and location
        current_time = end
        current_location = friend['location']
    return True

def generate_itinerary(perm, travel_times):
    current_time = 540
    current_location = 'Golden Gate Park'
    itinerary = []
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        start = max(arrival_time, friend['start'])
        end = start + friend['required']
        # Append to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': to_time_str(start),
            'end_time': to_time_str(end)
        })
        current_time = end
        current_location = friend['location']
    return itinerary

travel_times = {
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Sunset District': 10,
        'Marina District': 16,
        'Financial District': 26,
        'Union Square': 22,
    },
    'Haight-Ashbury': {
        'Golden Gate Park': 7,
        'Sunset District': 15,
        'Marina District': 17,
        'Financial District': 21,
        'Union Square': 17,
    },
    'Sunset District': {
        'Golden Gate Park': 11,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Financial District': 30,
        'Union Square': 30,
    },
    'Marina District': {
        'Golden Gate Park': 18,
        'Haight-Ashbury': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Union Square': 16,
    },
    'Financial District': {
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Sunset District': 31,
        'Marina District': 15,
        'Union Square': 9,
    },
    'Union Square': {
        'Golden Gate Park': 22,
        'Haight-Ashbury': 18,
        'Sunset District': 26,
        'Marina District': 18,
        'Financial District': 9,
    },
}

friends = [
    {'name': 'Sarah', 'location': 'Haight-Ashbury', 'start': 1020, 'end': 1290, 'required': 105},
    {'name': 'Patricia', 'location': 'Sunset District', 'start': 1020, 'end': 1185, 'required': 45},
    {'name': 'Matthew', 'location': 'Marina District', 'start': 555, 'end': 720, 'required': 15},
    {'name': 'Joseph', 'location': 'Financial District', 'start': 855, 'end': 1125, 'required': 30},
    {'name': 'Robert', 'location': 'Union Square', 'start': 615, 'end': 1305, 'required': 15}
]

# Generate all possible subsets in order of decreasing size
for subset_size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        for perm in itertools.permutations(subset):
            if is_feasible(perm, travel_times):
                itinerary = generate_itinerary(perm, travel_times)
                result = {"itinerary": itinerary}
                print(json.dumps(result))
                exit()

# If no solution found (unlikely given the problem constraints)
print(json.dumps({"itinerary": []}))
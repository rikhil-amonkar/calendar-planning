import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

locations = ['Fisherman\'s Wharf', 'Golden Gate Park', 'Presidio', 'Richmond District']

travel_times = [
    [0, 25, 17, 18],
    [24, 0, 11, 7],
    [19, 12, 0, 7],
    [18, 9, 7, 0]
]

friends = [
    {
        'name': 'Melissa',
        'location': 1,
        'available_start': 510,  # 8:30 AM
        'available_end': 1200,   # 8:00 PM
        'required_duration': 15
    },
    {
        'name': 'Nancy',
        'location': 2,
        'available_start': 1185,  # 7:45 PM
        'available_end': 1320,    # 10:00 PM
        'required_duration': 105
    },
    {
        'name': 'Emily',
        'location': 3,
        'available_start': 1005,  # 4:45 PM
        'available_end': 1320,    # 10:00 PM
        'required_duration': 120
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 0  # Fisherman's Wharf
    itinerary = []
    valid = True
    for friend in perm:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Determine earliest possible start time
        earliest_start = max(arrival_time, friend['available_start'])
        required_duration = friend['required_duration']
        end_time = earliest_start + required_duration
        # Check if meeting is possible
        if end_time > friend['available_end']:
            valid = False
            break
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': locations[friend['location']],
            'person': friend['name'],
            'start_time': minutes_to_time(earliest_start),
            'end_time': minutes_to_time(end_time)
        })
        # Update current time and location
        current_time = end_time
        current_location = friend['location']
    if valid:
        # Output the JSON
        print(json.dumps({"itinerary": itinerary}))
        exit()

# If no valid permutation found (though there should be some)
print(json.dumps({"itinerary": []}))
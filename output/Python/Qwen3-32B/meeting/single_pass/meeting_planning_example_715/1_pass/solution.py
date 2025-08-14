import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Presidio': {
        'Marina District': 11,
        'The Castro': 21,
        'Fisherman\'s Wharf': 19,
        'Bayview': 31,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Alamo Square': 19,
        'Golden Gate Park': 12,
    },
    'Marina District': {
        'Presidio': 10,
        'The Castro': 22,
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Pacific Heights': 7,
        'Mission District': 20,
        'Alamo Square': 15,
        'Golden Gate Park': 18,
    },
    'The Castro': {
        'Presidio': 20,
        'Marina District': 21,
        'Fisherman\'s Wharf': 24,
        'Bayview': 19,
        'Pacific Heights': 16,
        'Mission District': 7,
        'Alamo Square': 8,
        'Golden Gate Park': 11,
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Marina District': 9,
        'The Castro': 27,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Mission District': 22,
        'Alamo Square': 21,
        'Golden Gate Park': 25,
    },
    'Bayview': {
        'Presidio': 32,
        'Marina District': 27,
        'The Castro': 19,
        'Fisherman\'s Wharf': 25,
        'Pacific Heights': 23,
        'Mission District': 13,
        'Alamo Square': 16,
        'Golden Gate Park': 22,
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Marina District': 6,
        'The Castro': 16,
        'Fisherman\'s Wharf': 13,
        'Bayview': 22,
        'Mission District': 15,
        'Alamo Square': 10,
        'Golden Gate Park': 15,
    },
    'Mission District': {
        'Presidio': 25,
        'Marina District': 19,
        'The Castro': 7,
        'Fisherman\'s Wharf': 22,
        'Bayview': 14,
        'Pacific Heights': 16,
        'Alamo Square': 11,
        'Golden Gate Park': 17,
    },
    'Alamo Square': {
        'Presidio': 17,
        'Marina District': 15,
        'The Castro': 8,
        'Fisherman\'s Wharf': 19,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Golden Gate Park': 9,
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Marina District': 16,
        'The Castro': 13,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Mission District': 17,
        'Alamo Square': 9,
    },
}

friends = [
    {'name': 'Joseph', 'location': 'Golden Gate Park', 'available_start': 510, 'available_end': 1275, 'required_duration': 105},
    {'name': 'Melissa', 'location': 'The Castro', 'available_start': 570, 'available_end': 1140, 'required_duration': 30},
    {'name': 'Robert', 'location': 'Alamo Square', 'available_start': 675, 'available_end': 1050, 'required_duration': 120},
    {'name': 'Matthew', 'location': 'Bayview', 'available_start': 615, 'available_end': 795, 'required_duration': 30},
    {'name': 'Jeffrey', 'location': 'Fisherman\'s Wharf', 'available_start': 765, 'available_end': 1125, 'required_duration': 120},
    {'name': 'Amanda', 'location': 'Marina District', 'available_start': 885, 'available_end': 1170, 'required_duration': 105},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'available_start': 1020, 'available_end': 1290, 'required_duration': 105},
    {'name': 'Karen', 'location': 'Mission District', 'available_start': 1050, 'available_end': 1230, 'required_duration': 105},
]

def is_feasible(perm):
    current_time = 540  # 9:00 AM
    current_location = 'Presidio'
    for friend in perm:
        # Get travel time from current_location to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Earliest start is max of arrival time and friend's available start
        earliest_start = max(arrival_time, friend['available_start'])
        # Latest possible start is available_end - required_duration
        latest_start = friend['available_end'] - friend['required_duration']
        if earliest_start > latest_start:
            return False
        # Update current time and location
        current_time = earliest_start + friend['required_duration']
        current_location = friend['location']
    return True

def generate_itinerary(perm):
    current_time = 540
    current_location = 'Presidio'
    itinerary = []
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        earliest_start = max(arrival_time, friend['available_start'])
        latest_start = friend['available_end'] - friend['required_duration']
        meeting_start = earliest_start
        meeting_end = meeting_start + friend['required_duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    return itinerary

for k in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, k):
        for perm in itertools.permutations(subset):
            if is_feasible(perm):
                itinerary = generate_itinerary(perm)
                result = {"itinerary": itinerary}
                print(json.dumps(result))
                exit()

# If no itinerary found (unlikely)
print(json.dumps({"itinerary": []}))
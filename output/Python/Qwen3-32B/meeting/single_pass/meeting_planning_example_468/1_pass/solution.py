import itertools
import json

friends = [
    {'name': 'Rebecca', 'location': 'Bayview', 'start': 540, 'end': 765},
    {'name': 'Amanda', 'location': 'Pacific Heights', 'start': 1110, 'end': 1305},
    {'name': 'James', 'location': 'Alamo Square', 'start': 585, 'end': 1275},
    {'name': 'Sarah', 'location': "Fisherman's Wharf", 'start': 480, 'end': 1290},
    {'name': 'Melissa', 'location': 'Golden Gate Park', 'start': 540, 'end': 1125},
]

travel_times = {
    'The Castro': {
        'Bayview': 19,
        'Pacific Heights': 16,
        'Alamo Square': 8,
        "Fisherman's Wharf": 24,
        'Golden Gate Park': 11,
    },
    'Bayview': {
        'The Castro': 20,
        'Pacific Heights': 23,
        'Alamo Square': 16,
        "Fisherman's Wharf": 25,
        'Golden Gate Park': 22,
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Bayview': 22,
        'Alamo Square': 10,
        "Fisherman's Wharf": 13,
        'Golden Gate Park': 15,
    },
    'Alamo Square': {
        'The Castro': 8,
        'Bayview': 16,
        'Pacific Heights': 10,
        "Fisherman's Wharf": 19,
        'Golden Gate Park': 9,
    },
    "Fisherman's Wharf": {
        'The Castro': 26,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Alamo Square': 20,
        'Golden Gate Park': 25,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Alamo Square': 10,
        "Fisherman's Wharf": 24,
    },
}

def is_feasible(perm):
    current_time = 540  # Start at 9:00 AM
    current_location = 'The Castro'
    for friend in perm:
        loc = friend['location']
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time
        friend_start = friend['start']
        friend_end = friend['end']
        latest_start = friend_end - 90
        earliest_start = max(arrival_time, friend_start)
        if earliest_start > latest_start:
            return False
        current_time = earliest_start + 90
        current_location = loc
    return True

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_optimal_schedule():
    for subset_size in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, subset_size):
            permutations = itertools.permutations(subset)
            for perm in permutations:
                if is_feasible(perm):
                    # Found a feasible permutation
                    itinerary = []
                    current_time = 540
                    current_location = 'The Castro'
                    for friend in perm:
                        loc = friend['location']
                        travel_time = travel_times[current_location][loc]
                        arrival_time = current_time + travel_time
                        friend_start = friend['start']
                        friend_end = friend['end']
                        latest_start = friend_end - 90
                        earliest_start = max(arrival_time, friend_start)
                        end_time = earliest_start + 90
                        itinerary.append({
                            'action': 'meet',
                            'location': loc,
                            'person': friend['name'],
                            'start_time': minutes_to_time(earliest_start),
                            'end_time': minutes_to_time(end_time)
                        })
                        current_time = end_time
                        current_location = loc
                    return {
                        'itinerary': itinerary
                    }
    # If no friends can be met
    return {"itinerary": []}

result = find_optimal_schedule()
print(json.dumps(result, indent=2))
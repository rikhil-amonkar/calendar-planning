import itertools
import json

def time_str_to_min(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def min_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Financial District': 30
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Presidio': 18,
        'Financial District': 17
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Presidio': 14,
        'Financial District': 11
    },
    'Presidio': {
        'Sunset District': 15,
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Financial District': 23
    },
    'Financial District': {
        'Sunset District': 31,
        'Alamo Square': 17,
        'Russian Hill': 10,
        'Presidio': 22
    }
}

friends = [
    {
        'name': 'Kevin',
        'location': 'Alamo Square',
        'available_start': '8:15',
        'available_end': '21:30',
        'required_duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Russian Hill',
        'available_start': '8:45',
        'available_end': '12:30',
        'required_duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'available_start': '18:30',
        'available_end': '19:15',
        'required_duration': 45
    },
    {
        'name': 'Thomas',
        'location': 'Financial District',
        'available_start': '19:00',
        'available_end': '21:45',
        'required_duration': 45
    }
]

def is_feasible(perm):
    current_time = time_str_to_min('9:00')  # start at 9:00 AM
    current_location = 'Sunset District'
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        friend_start = time_str_to_min(friend['available_start'])
        friend_end = time_str_to_min(friend['available_end'])
        required = friend['required_duration']
        earliest_start = max(arrival_time, friend_start)
        if earliest_start + required > friend_end:
            return False
        current_time = earliest_start + required
        current_location = friend['location']
    return True

best_itinerary = None

for subset_size in range(4, 0, -1):
    for perm in itertools.permutations(friends, subset_size):
        if is_feasible(perm):
            current_time = time_str_to_min('9:00')
            current_location = 'Sunset District'
            itinerary = []
            for friend in perm:
                travel_time = travel_times[current_location][friend['location']]
                arrival_time = current_time + travel_time
                friend_start = time_str_to_min(friend['available_start'])
                friend_end = time_str_to_min(friend['available_end'])
                required = friend['required_duration']
                earliest_start = max(arrival_time, friend_start)
                start_time_str = min_to_time_str(earliest_start)
                end_time_str = min_to_time_str(earliest_start + required)
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': start_time_str,
                    'end_time': end_time_str
                })
                current_time = earliest_start + required
                current_location = friend['location']
            best_itinerary = itinerary
            break
        # else continue
    if best_itinerary is not None:
        break

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
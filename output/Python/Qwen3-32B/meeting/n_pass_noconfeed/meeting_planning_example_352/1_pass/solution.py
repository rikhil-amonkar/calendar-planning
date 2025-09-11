import itertools
import json

def time_str_to_mins(s):
    h, m = map(int, s.split(':'))
    return h * 60 + m

def mins_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def is_feasible(perm, travel_times):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Union Square'
    itinerary = []
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time

        available_start = time_str_to_mins(friend['available_start'])
        available_end = time_str_to_mins(friend['available_end'])

        start_time = max(arrival_time, available_start)

        if start_time + friend['meeting_duration'] > available_end:
            return False, None

        end_time = start_time + friend['meeting_duration']

        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': mins_to_time_str(start_time),
            'end_time': mins_to_time_str(end_time)
        })

        current_time = end_time
        current_location = friend['location']

    return True, itinerary

travel_times = {
    'Union Square': {
        'Nob Hill': 9,
        'Haight-Ashbury': 18,
        'Chinatown': 7,
        'Marina District': 18,
    },
    'Nob Hill': {
        'Union Square': 7,
        'Haight-Ashbury': 13,
        'Chinatown': 6,
        'Marina District': 11,
    },
    'Haight-Ashbury': {
        'Union Square': 17,
        'Nob Hill': 15,
        'Chinatown': 19,
        'Marina District': 17,
    },
    'Chinatown': {
        'Union Square': 7,
        'Nob Hill': 8,
        'Haight-Ashbury': 19,
        'Marina District': 12,
    },
    'Marina District': {
        'Union Square': 16,
        'Nob Hill': 12,
        'Haight-Ashbury': 16,
        'Chinatown': 16,
    }
}

friends = [
    {
        'name': 'Karen',
        'location': 'Nob Hill',
        'available_start': '9:15',
        'available_end': '9:45',
        'meeting_duration': 30,
    },
    {
        'name': 'Joseph',
        'location': 'Haight-Ashbury',
        'available_start': '12:30',
        'available_end': '19:45',
        'meeting_duration': 90,
    },
    {
        'name': 'Sandra',
        'location': 'Chinatown',
        'available_start': '7:15',
        'available_end': '19:15',
        'meeting_duration': 75,
    },
    {
        'name': 'Nancy',
        'location': 'Marina District',
        'available_start': '11:00',
        'available_end': '20:15',
        'meeting_duration': 105,
    }
]

optimal_itinerary = None

for size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, size):
        for perm in itertools.permutations(subset):
            feasible, itinerary = is_feasible(perm, travel_times)
            if feasible:
                optimal_itinerary = itinerary
                break
        if optimal_itinerary:
            break
    if optimal_itinerary:
        break

result = {"itinerary": optimal_itinerary}
print(json.dumps(result, indent=2))
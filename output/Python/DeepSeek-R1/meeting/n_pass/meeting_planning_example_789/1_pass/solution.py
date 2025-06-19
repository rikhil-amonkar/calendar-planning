import itertools
import json

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Union Square': {
        'Russian Hill': 13, 'Alamo Square': 15, 'Haight-Ashbury': 18, 'Marina District': 18,
        'Bayview': 15, 'Chinatown': 7, 'Presidio': 24, 'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10, 'Alamo Square': 15, 'Haight-Ashbury': 17, 'Marina District': 7,
        'Bayview': 23, 'Chinatown': 9, 'Presidio': 14, 'Sunset District': 23
    },
    'Alamo Square': {
        'Union Square': 14, 'Russian Hill': 13, 'Haight-Ashbury': 5, 'Marina District': 15,
        'Bayview': 16, 'Chinatown': 15, 'Presidio': 17, 'Sunset District': 16
    },
    'Haight-Ashbury': {
        'Union Square': 19, 'Russian Hill': 17, 'Alamo Square': 5, 'Marina District': 17,
        'Bayview': 18, 'Chinatown': 19, 'Presidio': 15, 'Sunset District': 15
    },
    'Marina District': {
        'Union Square': 16, 'Russian Hill': 8, 'Alamo Square': 15, 'Haight-Ashbury': 16,
        'Bayview': 27, 'Chinatown': 15, 'Presidio': 10, 'Sunset District': 19
    },
    'Bayview': {
        'Union Square': 18, 'Russian Hill': 23, 'Alamo Square': 16, 'Haight-Ashbury': 19,
        'Marina District': 27, 'Chinatown': 19, 'Presidio': 32, 'Sunset District': 23
    },
    'Chinatown': {
        'Union Square': 7, 'Russian Hill': 7, 'Alamo Square': 17, 'Haight-Ashbury': 19,
        'Marina District': 12, 'Bayview': 20, 'Presidio': 19, 'Sunset District': 29
    },
    'Presidio': {
        'Union Square': 22, 'Russian Hill': 14, 'Alamo Square': 19, 'Haight-Ashbury': 15,
        'Marina District': 11, 'Bayview': 31, 'Chinatown': 21, 'Sunset District': 15
    },
    'Sunset District': {
        'Union Square': 30, 'Russian Hill': 24, 'Alamo Square': 17, 'Haight-Ashbury': 15,
        'Marina District': 21, 'Bayview': 22, 'Chinatown': 30, 'Presidio': 16
    }
}

friends = [
    {'name': 'Betty', 'location': 'Russian Hill', 'start_avail': 420, 'end_avail': 1005, 'min_duration': 105},
    {'name': 'Melissa', 'location': 'Alamo Square', 'start_avail': 570, 'end_avail': 1035, 'min_duration': 105},
    {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start_avail': 735, 'end_avail': 1140, 'min_duration': 90},
    {'name': 'Jeffrey', 'location': 'Marina District', 'start_avail': 735, 'end_avail': 1080, 'min_duration': 45},
    {'name': 'James', 'location': 'Bayview', 'start_avail': 450, 'end_avail': 1200, 'min_duration': 90},
    {'name': 'Anthony', 'location': 'Chinatown', 'start_avail': 705, 'end_avail': 810, 'min_duration': 75},
    {'name': 'Timothy', 'location': 'Presidio', 'start_avail': 750, 'end_avail': 885, 'min_duration': 90},
    {'name': 'Emily', 'location': 'Sunset District', 'start_avail': 1170, 'end_avail': 1290, 'min_duration': 120}
]

start_time = 540
start_location = 'Union Square'
found = False
result_itinerary = []

for k in range(len(friends), 0, -1):
    if found:
        break
    for subset in itertools.combinations(friends, k):
        if found:
            break
        for perm in itertools.permutations(subset):
            current_time = start_time
            current_loc = start_location
            itinerary = []
            feasible = True
            for friend in perm:
                if current_loc == friend['location']:
                    travel = 0
                else:
                    travel = travel_times[current_loc][friend['location']]
                arrival = current_time + travel
                start_meeting = max(arrival, friend['start_avail'])
                end_meeting = start_meeting + friend['min_duration']
                if end_meeting > friend['end_avail']:
                    feasible = False
                    break
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": min_to_time(start_meeting),
                    "end_time": min_to_time(end_meeting)
                })
                current_time = end_meeting
                current_loc = friend['location']
            if feasible:
                result_itinerary = itinerary
                found = True
                break

print(json.dumps({"itinerary": result_itinerary}))
import itertools
import json

friends_data = [
    {'name': 'Betty', 'location': 'Russian Hill', 'start': 420, 'end': 1005, 'duration': 105},
    {'name': 'Melissa', 'location': 'Alamo Square', 'start': 570, 'end': 1035, 'duration': 105},
    {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start': 735, 'end': 1140, 'duration': 90},
    {'name': 'Jeffrey', 'location': 'Marina District', 'start': 735, 'end': 1080, 'duration': 45},
    {'name': 'James', 'location': 'Bayview', 'start': 450, 'end': 1200, 'duration': 90},
    {'name': 'Anthony', 'location': 'Chinatown', 'start': 705, 'end': 810, 'duration': 75},
    {'name': 'Timothy', 'location': 'Presidio', 'start': 750, 'end': 885, 'duration': 90},
    {'name': 'Emily', 'location': 'Sunset District', 'start': 1170, 'end': 1290, 'duration': 120},
]

travel_times = {
    'Union Square': {
        'Russian Hill': 13,
        'Alamo Square': 15,
        'Haight-Ashbury': 18,
        'Marina District': 18,
        'Bayview': 15,
        'Chinatown': 7,
        'Presidio': 24,
        'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10,
        'Alamo Square': 15,
        'Haight-Ashbury': 17,
        'Marina District': 7,
        'Bayview': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Sunset District': 23
    },
    'Alamo Square': {
        'Union Square': 14,
        'Russian Hill': 13,
        'Haight-Ashbury': 5,
        'Marina District': 15,
        'Bayview': 16,
        'Chinatown': 15,
        'Presidio': 17,
        'Sunset District': 16
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'Russian Hill': 17,
        'Alamo Square': 5,
        'Marina District': 17,
        'Bayview': 18,
        'Chinatown': 19,
        'Presidio': 15,
        'Sunset District': 15
    },
    'Marina District': {
        'Union Square': 16,
        'Russian Hill': 8,
        'Alamo Square': 15,
        'Haight-Ashbury': 16,
        'Bayview': 27,
        'Chinatown': 15,
        'Presidio': 10,
        'Sunset District': 19
    },
    'Bayview': {
        'Union Square': 18,
        'Russian Hill': 23,
        'Alamo Square': 16,
        'Haight-Ashbury': 19,
        'Marina District': 27,
        'Chinatown': 19,
        'Presidio': 32,
        'Sunset District': 23
    },
    'Chinatown': {
        'Union Square': 7,
        'Russian Hill': 7,
        'Alamo Square': 17,
        'Haight-Ashbury': 19,
        'Marina District': 12,
        'Bayview': 20,
        'Presidio': 19,
        'Sunset District': 29
    },
    'Presidio': {
        'Union Square': 22,
        'Russian Hill': 14,
        'Alamo Square': 19,
        'Haight-Ashbury': 15,
        'Marina District': 11,
        'Bayview': 31,
        'Chinatown': 21,
        'Sunset District': 15
    },
    'Sunset District': {
        'Union Square': 30,
        'Russian Hill': 24,
        'Alamo Square': 17,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Bayview': 22,
        'Chinatown': 30,
        'Presidio': 16
    }
}

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

max_count = 0
best_itinerary = []

for perm in itertools.permutations(friends_data):
    current_time = 540
    current_location = 'Union Square'
    itinerary = []
    for friend in perm:
        loc = friend['location']
        if current_location not in travel_times or loc not in travel_times[current_location]:
            break
        travel = travel_times[current_location][loc]
        arrival = current_time + travel
        arrival = max(arrival, friend['start'])
        if arrival >= friend['end']:
            continue
        end = arrival + friend['duration']
        if end > friend['end']:
            continue
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": friend['name'],
            "start_time": minutes_to_time(arrival),
            "end_time": minutes_to_time(end)
        })
        current_time = end
        current_location = loc
    if len(itinerary) > max_count:
        max_count = len(itinerary)
        best_itinerary = itinerary
    elif len(itinerary) == max_count and itinerary:
        current_last = current_time
        best_last = sum(int(t.split(':')[0])*60 + int(t.split(':')[1]) for entry in best_itinerary[-1:]) if best_itinerary else 0
        if current_last < best_last or not best_itinerary:
            best_itinerary = itinerary

print(json.dumps({"itinerary": best_itinerary}, indent=2))
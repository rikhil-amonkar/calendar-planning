import itertools
import json

friends = [
    {
        'name': 'Sarah',
        'location': 'Haight-Ashbury',
        'start': 17 * 60,
        'end': 21 * 60 + 30,
        'duration': 105
    },
    {
        'name': 'Patricia',
        'location': 'Sunset District',
        'start': 17 * 60,
        'end': 19 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Marina District',
        'start': 9 * 60 + 15,
        'end': 12 * 60,
        'duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'start': 14 * 60 + 15,
        'end': 18 * 60 + 45,
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Union Square',
        'start': 10 * 60 + 15,
        'end': 21 * 60 + 45,
        'duration': 15
    }
]

travel_matrix = {
    'Golden Gate Park': {'Haight-Ashbury':7, 'Sunset District':10, 'Marina District':16, 'Financial District':26, 'Union Square':22},
    'Haight-Ashbury': {'Golden Gate Park':7, 'Sunset District':15, 'Marina District':17, 'Financial District':21, 'Union Square':17},
    'Sunset District': {'Golden Gate Park':11, 'Haight-Ashbury':15, 'Marina District':21, 'Financial District':30, 'Union Square':30},
    'Marina District': {'Golden Gate Park':18, 'Haight-Ashbury':16, 'Sunset District':19, 'Financial District':17, 'Union Square':16},
    'Financial District': {'Golden Gate Park':23, 'Haight-Ashbury':19, 'Sunset District':31, 'Marina District':15, 'Union Square':9},
    'Union Square': {'Golden Gate Park':22, 'Haight-Ashbury':18, 'Sunset District':26, 'Marina District':18, 'Financial District':9},
}

def min_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02}"

best_count = 0
best_itinerary = []
best_end_time = float('inf')

for perm in itertools.permutations(friends):
    current_location = 'Golden Gate Park'
    current_time = 9 * 60
    itinerary = []
    count = 0
    for friend in perm:
        try:
            travel_time = travel_matrix[current_location][friend['location']]
        except KeyError:
            break
        arrival_time = current_time + travel_time
        if arrival_time > friend['end']:
            break
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + friend['duration']
        if end_time > friend['end']:
            break
        itinerary.append({
            'friend': friend,
            'start': start_time,
            'end': end_time,
            'location': friend['location']
        })
        current_time = end_time
        current_location = friend['location']
        count += 1
    if count > best_count or (count == best_count and current_time < best_end_time):
        best_count = count
        best_itinerary = itinerary
        best_end_time = current_time

result = []
for entry in best_itinerary:
    friend = entry['friend']
    start = min_to_time_str(entry['start'])
    end = min_to_time_str(entry['end'])
    result.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start,
        "end_time": end
    })

print(json.dumps({"itinerary": result}, indent=2))
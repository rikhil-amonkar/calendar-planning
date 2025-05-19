import itertools
import json

friends = [
    {
        'name': 'Sarah',
        'location': 'North Beach',
        'available_start': 16.0,
        'available_end': 18.25,
        'duration': 1.0
    },
    {
        'name': 'Jeffrey',
        'location': 'Union Square',
        'available_start': 15.0,
        'available_end': 22.0,
        'duration': 1.25
    },
    {
        'name': 'Brian',
        'location': 'Alamo Square',
        'available_start': 16.0,
        'available_end': 17.5,
        'duration': 1.25
    }
]

travel_times = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
}

def float_to_time(t):
    hours = int(t)
    minutes = int(round((t - hours) * 60))
    if minutes == 60:
        hours += 1
        minutes = 0
    return f"{hours}:{minutes:02d}"

best_itinerary = []
max_friends = 0
min_total_time = float('inf')

for perm_length in range(1, 4):
    for perm in itertools.permutations(friends, perm_length):
        current_location = 'Sunset District'
        current_time = 9.0
        itinerary = []
        valid = True
        visited = set()
        
        for friend in perm:
            if friend['name'] in visited:
                valid = False
                break
            visited.add(friend['name'])
            key = (current_location, friend['location'])
            travel = travel_times.get(key)
            if travel is None:
                valid = False
                break
            arrival = current_time + travel / 60
            start = max(arrival, friend['available_start'])
            latest_start = friend['available_end'] - friend['duration']
            if start > latest_start:
                valid = False
                break
            end = start + friend['duration']
            if end > friend['available_end']:
                valid = False
                break
            itinerary.append((friend, start, end))
            current_time = end
            current_location = friend['location']
        
        if valid:
            num_friends = len(itinerary)
            if num_friends > max_friends or (num_friends == max_friends and current_time < min_total_time):
                max_friends = num_friends
                min_total_time = current_time
                best_itinerary = itinerary

output = []
for entry in best_itinerary:
    friend = entry[0]
    start = entry[1]
    end = entry[2]
    output.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": float_to_time(start),
        "end_time": float_to_time(end)
    })

print(json.dumps({"itinerary": output}, indent=2))
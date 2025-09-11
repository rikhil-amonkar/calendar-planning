import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Haight-Ashbury'): 17
}

friends = [
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'available_start': 11 * 60 + 45,
        'available_end': 14 * 60 + 45,
        'required_duration': 120
    },
    {
        'name': 'Elizabeth',
        'location': 'Financial District',
        'available_start': 10 * 60 + 0,
        'available_end': 12 * 60 + 45,
        'required_duration': 75
    },
    {
        'name': 'Karen',
        'location': 'Mission District',
        'available_start': 14 * 60 + 15,
        'available_end': 22 * 60 + 0,
        'required_duration': 30
    },
    {
        'name': 'Richard',
        'location': 'Fisherman\'s Wharf',
        'available_start': 14 * 60 + 30,
        'available_end': 17 * 60 + 30,
        'required_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Presidio',
        'available_start': 21 * 60 + 45,
        'available_end': 22 * 60 + 45,
        'required_duration': 60
    },
    {
        'name': 'Helen',
        'location': 'Sunset District',
        'available_start': 14 * 60 + 45,
        'available_end': 20 * 60 + 45,
        'required_duration': 105
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'available_start': 14 * 60 + 15,
        'available_end': 17 * 60 + 30,
        'required_duration': 105
    },
    {
        'name': 'Ashley',
        'location': 'Russian Hill',
        'available_start': 11 * 60 + 30,
        'available_end': 21 * 60 + 30,
        'required_duration': 45
    }
]

best_path = []

def explore(current_time, current_location, visited, path):
    global best_path
    if len(path) > len(best_path):
        best_path = path.copy()
    for friend in friends:
        if friend['name'] in visited:
            continue
        from_loc = current_location
        to_loc = friend['location']
        if (from_loc, to_loc) not in travel_times:
            continue
        travel_duration = travel_times[(from_loc, to_loc)]
        arrival_time = current_time + travel_duration
        s = friend['available_start']
        e = friend['available_end']
        required = friend['required_duration']
        start_time = max(arrival_time, s)
        if start_time + required <= e:
            new_visited = visited.copy()
            new_visited.add(friend['name'])
            new_path = path + [friend]
            new_time = start_time + required
            explore(new_time, to_loc, new_visited, new_path)

# Initial call
initial_time = 9 * 60  # 9:00 AM
initial_location = 'Marina District'
explore(initial_time, initial_location, set(), [])

# Generate itinerary
itinerary = []
current_time = initial_time
current_location = initial_location

for friend in best_path:
    to_loc = friend['location']
    travel_duration = travel_times.get((current_location, to_loc), 0)
    arrival_time = current_time + travel_duration
    s = friend['available_start']
    start_time = max(arrival_time, s)
    end_time = start_time + friend['required_duration']
    itinerary.append({
        'action': 'meet',
        'location': to_loc,
        'person': friend['name'],
        'start_time': time_to_str(start_time),
        'end_time': time_to_str(end_time)
    })
    current_time = end_time
    current_location = to_loc

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))
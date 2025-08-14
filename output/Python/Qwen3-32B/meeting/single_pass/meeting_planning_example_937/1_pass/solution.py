import json

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_time = {
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Presidio'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Presidio'): 17,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Alamo Square'): 19,
}

friends = [
    {
        'name': 'David',
        'location': 'Sunset District',
        'start_time': 555,
        'end_time': 1320,
        'required': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'start_time': 1275,
        'end_time': 1305,
        'required': 15
    },
    {
        'name': 'Patricia',
        'location': 'Nob Hill',
        'start_time': 900,
        'end_time': 1155,
        'required': 120
    },
    {
        'name': 'Mary',
        'location': 'Marina District',
        'start_time': 885,
        'end_time': 1005,
        'required': 45
    },
    {
        'name': 'Charles',
        'location': 'Richmond District',
        'start_time': 1035,
        'end_time': 1260,
        'required': 15
    },
    {
        'name': 'Joshua',
        'location': 'Financial District',
        'start_time': 870,
        'end_time': 1035,
        'required': 90
    },
    {
        'name': 'Ronald',
        'location': 'Embarcadero',
        'start_time': 1095,
        'end_time': 1245,
        'required': 30
    },
    {
        'name': 'George',
        'location': 'The Castro',
        'start_time': 855,
        'end_time': 1140,
        'required': 105
    },
    {
        'name': 'Kimberly',
        'location': 'Alamo Square',
        'start_time': 540,
        'end_time': 870,
        'required': 105
    },
    {
        'name': 'William',
        'location': 'Presidio',
        'start_time': 420,
        'end_time': 765,
        'required': 60
    }
]

best_path = []

def backtrack(current_location, current_time, visited, path):
    global best_path
    for i in range(len(friends)):
        if i not in visited:
            friend = friends[i]
            location = friend['location']
            travel_duration = travel_time.get((current_location, location), float('inf'))
            if travel_duration == float('inf'):
                continue
            arrival_time = current_time + travel_duration
            friend_start = friend['start_time']
            friend_end = friend['end_time']
            required = friend['required']
            if arrival_time > friend_end:
                continue
            possible_start = max(arrival_time, friend_start)
            if possible_start + required > friend_end:
                continue
            new_time = possible_start + required
            new_visited = visited.copy()
            new_visited.add(i)
            new_path = path + [(i, possible_start, new_time)]
            if len(new_path) > len(best_path):
                best_path = new_path.copy()
            backtrack(location, new_time, new_visited, new_path)

backtrack('Russian Hill', 540, set(), [])

itinerary = []
for idx, start, end in best_path:
    friend = friends[idx]
    entry = {
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': convert_minutes_to_time(start),
        'end_time': convert_minutes_to_time(end)
    }
    itinerary.append(entry)

result = {
    'itinerary': itinerary
}

print(json.dumps(result, indent=2))
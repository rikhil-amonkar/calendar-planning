import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends
friends = [
    {
        'name': 'Daniel',
        'location': 'Nob Hill',
        'available_start': 495,  # 8:15 AM
        'available_end': 660,    # 11:00 AM
        'required': 15
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'available_start': 720,  # 12:00 PM
        'available_end': 1080,   # 6:00 PM
        'required': 90
    },
    {
        'name': 'Kevin',
        'location': 'Chinatown',
        'available_start': 720,
        'available_end': 1140,   # 7:00 PM
        'required': 30
    },
    {
        'name': 'Betty',
        'location': 'Richmond District',
        'available_start': 795,  # 1:15 PM
        'available_end': 945,    # 3:45 PM
        'required': 30
    },
    {
        'name': 'Steven',
        'location': 'Marina District',
        'available_start': 990,  # 4:30 PM
        'available_end': 1245,   # 8:45 PM
        'required': 90
    },
    {
        'name': 'Elizabeth',
        'location': 'Presidio',
        'available_start': 1275, # 9:15 PM
        'available_end': 1335,   # 10:15 PM
        'required': 45
    },
    {
        'name': 'Ashley',
        'location': 'Golden Gate Park',
        'available_start': 1245, # 8:45 PM
        'available_end': 1305,   # 9:45 PM
        'required': 60
    },
    {
        'name': 'Lisa',
        'location': 'The Castro',
        'available_start': 1155, # 7:15 PM
        'available_end': 1275,   # 9:15 PM
        'required': 120
    }
]

# Define travel times
travel_data = [
    ('Mission District', 'The Castro', 7),
    ('Mission District', 'Nob Hill', 12),
    ('Mission District', 'Presidio', 25),
    ('Mission District', 'Marina District', 19),
    ('Mission District', 'Pacific Heights', 16),
    ('Mission District', 'Golden Gate Park', 17),
    ('Mission District', 'Chinatown', 16),
    ('Mission District', 'Richmond District', 20),
    ('The Castro', 'Mission District', 7),
    ('The Castro', 'Nob Hill', 16),
    ('The Castro', 'Presidio', 20),
    ('The Castro', 'Marina District', 21),
    ('The Castro', 'Pacific Heights', 16),
    ('The Castro', 'Golden Gate Park', 11),
    ('The Castro', 'Chinatown', 22),
    ('The Castro', 'Richmond District', 16),
    ('Nob Hill', 'Mission District', 13),
    ('Nob Hill', 'The Castro', 17),
    ('Nob Hill', 'Presidio', 17),
    ('Nob Hill', 'Marina District', 11),
    ('Nob Hill', 'Pacific Heights', 8),
    ('Nob Hill', 'Golden Gate Park', 17),
    ('Nob Hill', 'Chinatown', 6),
    ('Nob Hill', 'Richmond District', 14),
    ('Presidio', 'Mission District', 26),
    ('Presidio', 'The Castro', 21),
    ('Presidio', 'Nob Hill', 18),
    ('Presidio', 'Marina District', 11),
    ('Presidio', 'Pacific Heights', 11),
    ('Presidio', 'Golden Gate Park', 12),
    ('Presidio', 'Chinatown', 21),
    ('Presidio', 'Richmond District', 7),
    ('Marina District', 'Mission District', 20),
    ('Marina District', 'The Castro', 22),
    ('Marina District', 'Nob Hill', 12),
    ('Marina District', 'Presidio', 10),
    ('Marina District', 'Pacific Heights', 7),
    ('Marina District', 'Golden Gate Park', 18),
    ('Marina District', 'Chinatown', 15),
    ('Marina District', 'Richmond District', 11),
    ('Pacific Heights', 'Mission District', 15),
    ('Pacific Heights', 'The Castro', 16),
    ('Pacific Heights', 'Nob Hill', 8),
    ('Pacific Heights', 'Presidio', 11),
    ('Pacific Heights', 'Marina District', 6),
    ('Pacific Heights', 'Golden Gate Park', 15),
    ('Pacific Heights', 'Chinatown', 11),
    ('Pacific Heights', 'Richmond District', 12),
    ('Golden Gate Park', 'Mission District', 17),
    ('Golden Gate Park', 'The Castro', 13),
    ('Golden Gate Park', 'Nob Hill', 20),
    ('Golden Gate Park', 'Presidio', 11),
    ('Golden Gate Park', 'Marina District', 16),
    ('Golden Gate Park', 'Pacific Heights', 16),
    ('Golden Gate Park', 'Chinatown', 23),
    ('Golden Gate Park', 'Richmond District', 7),
    ('Chinatown', 'Mission District', 17),
    ('Chinatown', 'The Castro', 22),
    ('Chinatown', 'Nob Hill', 9),
    ('Chinatown', 'Presidio', 19),
    ('Chinatown', 'Marina District', 12),
    ('Chinatown', 'Pacific Heights', 10),
    ('Chinatown', 'Golden Gate Park', 23),
    ('Chinatown', 'Richmond District', 20),
    ('Richmond District', 'Mission District', 20),
    ('Richmond District', 'The Castro', 16),
    ('Richmond District', 'Nob Hill', 17),
    ('Richmond District', 'Presidio', 7),
    ('Richmond District', 'Marina District', 9),
    ('Richmond District', 'Pacific Heights', 10),
    ('Richmond District', 'Golden Gate Park', 9),
    ('Richmond District', 'Chinatown', 20),
]

travel_times = {}
for from_loc, to_loc, time in travel_data:
    if from_loc not in travel_times:
        travel_times[from_loc] = {}
    travel_times[from_loc][to_loc] = time

best_itinerary = []
max_count = 0
best_end_time = float('inf')

for k in range(1, len(friends)+1):
    for perm in itertools.permutations(friends, k):
        current_time = 540  # 9:00 AM
        previous_location = 'Mission District'
        valid = True
        itinerary = []
        for friend in perm:
            to_location = friend['location']
            if previous_location not in travel_times or to_location not in travel_times[previous_location]:
                valid = False
                break
            travel_time = travel_times[previous_location][to_location]
            arrival_time = current_time + travel_time
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required']
            if arrival_time > available_end:
                valid = False
                break
            start_time = max(arrival_time, available_start)
            end_time = start_time + required
            if end_time > available_end:
                valid = False
                break
            itinerary.append({
                'action': 'meet',
                'location': to_location,
                'person': friend['name'],
                'start_time': start_time,
                'end_time': end_time
            })
            current_time = end_time
            previous_location = to_location
        if valid:
            count = len(itinerary)
            if count > max_count or (count == max_count and current_time < best_end_time):
                max_count = count
                best_itinerary = itinerary
                best_end_time = current_time

# Convert best itinerary to required format
result = {
    "itinerary": [
        {
            "action": "meet",
            "location": entry['location'],
            "person": entry['person'],
            "start_time": to_time_str(entry['start_time']),
            "end_time": to_time_str(entry['end_time'])
        }
        for entry in best_itinerary
    ]
}

print(json.dumps(result, indent=2))
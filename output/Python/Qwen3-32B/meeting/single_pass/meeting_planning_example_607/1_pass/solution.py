import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 20 * 60 + 45,  # 1245
        'available_end': 21 * 60 + 45,    # 1305
        'required_duration': 60
    },
    {
        'name': 'Jessica',
        'location': 'The Castro',
        'available_start': 15 * 60 + 45,   # 945
        'available_end': 19 * 60 + 30,     # 1170
        'required_duration': 60
    },
    {
        'name': 'Matthew',
        'location': 'Richmond District',
        'available_start': 7 * 60 + 30,    # 450
        'available_end': 15 * 60 + 15,     # 915
        'required_duration': 15
    },
    {
        'name': 'Michelle',
        'location': 'Marina District',
        'available_start': 10 * 60 + 30,   # 630
        'available_end': 18 * 60 + 45,     # 1125
        'required_duration': 75
    },
    {
        'name': 'Carol',
        'location': 'North Beach',
        'available_start': 12 * 60 + 0,    # 720
        'available_end': 17 * 60 + 0,      # 1020
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'available_start': 10 * 60 + 45,   # 645
        'available_end': 14 * 60 + 15,     # 855
        'required_duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Golden Gate Park',
        'available_start': 10 * 60 + 45,   # 645
        'available_end': 22 * 60 + 0,      # 1320
        'required_duration': 90
    }
]

travel_time = {
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Golden Gate Park'): 18,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Union Square'): 22,
}

best_itinerary = []
max_count = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Sunset District'
    itinerary = []
    
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        travel_duration = travel_time[(from_loc, to_loc)]
        arrival_time = current_time + travel_duration
        
        friend_start = friend['available_start']
        friend_end = friend['available_end']
        required = friend['required_duration']
        
        earliest_start = max(arrival_time, friend_start)
        latest_start = friend_end - required
        
        if earliest_start <= latest_start:
            start_meeting = earliest_start
            end_meeting = start_meeting + required
            itinerary.append({
                'friend': friend,
                'start': start_meeting,
                'end': end_meeting
            })
            current_time = end_meeting
            current_location = to_loc
        else:
            break  # Can't meet this friend, stop processing this permutation
    
    if len(itinerary) > max_count:
        max_count = len(itinerary)
        best_itinerary = itinerary

# Convert best_itinerary to JSON format
itinerary_list = []
for entry in best_itinerary:
    friend = entry['friend']
    start_time = minutes_to_time_str(entry['start'])
    end_time = minutes_to_time_str(entry['end'])
    itinerary_list.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

result = {"itinerary": itinerary_list}

print(json.dumps(result, indent=2))
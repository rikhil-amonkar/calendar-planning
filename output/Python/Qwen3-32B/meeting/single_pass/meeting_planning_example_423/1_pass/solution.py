import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Brian',
        'location': 'Financial District',
        'start_time': 9 * 60 + 45,  # 585
        'end_time': 21 * 60 + 45,   # 1305
        'required': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Golden Gate Park',
        'start_time': 8 * 60 + 45,  # 525
        'end_time': 21 * 60 + 30,   # 1290
        'required': 105
    },
    {
        'name': 'Jason',
        'location': 'Richmond District',
        'start_time': 13 * 60 + 0,  # 780
        'end_time': 20 * 60 + 45,   # 1245
        'required': 90
    },
    {
        'name': 'Laura',
        'location': 'Union Square',
        'start_time': 14 * 60 + 15, # 855
        'end_time': 19 * 60 + 30,   # 1170
        'required': 75
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start_time': 18 * 60 + 45, # 1125
        'end_time': 20 * 60 + 15,   # 1215
        'required': 45
    }
]

travel_times = {
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Union Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
}

max_friends = 0
best_itinerary = []

for k in range(1, len(friends)+1):
    for perm in itertools.permutations(friends, k):
        current_time = 9 * 60  # 540 minutes
        current_location = 'Presidio'
        valid = True
        itinerary = []
        for friend in perm:
            # Get travel time
            travel_time = travel_times.get( (current_location, friend['location']) )
            if travel_time is None:
                valid = False
                break
            current_time += travel_time
            # Check if arrival time is after friend's end time
            if current_time > friend['end_time']:
                valid = False
                break
            # Determine meeting start time
            meeting_start = max(current_time, friend['start_time'])
            meeting_end = meeting_start + friend['required']
            if meeting_end > friend['end_time']:
                valid = False
                break
            # Add to itinerary
            itinerary.append( (friend, meeting_start, meeting_end) )
            current_time = meeting_end
            current_location = friend['location']
        if valid:
            if len(itinerary) > max_friends:
                max_friends = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == max_friends:
                # For tie-breaker, perhaps compare the first friend's start time, etc.
                # But for simplicity, keep the first found
                pass

# Convert best_itinerary to JSON structure
json_itinerary = []
for entry in best_itinerary:
    friend, start, end = entry
    json_itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": to_time_str(start),
        "end_time": to_time_str(end)
    })

result = {
    "itinerary": json_itinerary
}

print(json.dumps(result, indent=2))
import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Financial District'): 30,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Presidio'): 22,
}

friends = [
    {
        'name': 'Kevin',
        'location': 'Alamo Square',
        'available_start': 495,  # 8:15 AM
        'available_end': 1290,   # 9:30 PM
        'required': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Russian Hill',
        'available_start': 525,  # 8:45 AM
        'available_end': 750,    # 12:30 PM
        'required': 30
    },
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'available_start': 1110, # 6:30 PM
        'available_end': 1155,   # 7:15 PM
        'required': 45
    },
    {
        'name': 'Thomas',
        'location': 'Financial District',
        'available_start': 1140, # 7:00 PM
        'available_end': 1285,   # 9:45 PM
        'required': 45
    }
]

start_time_minutes = 540  # 9:00 AM
start_location = 'Sunset District'

best_itinerary = []
max_length = 0

for r in range(1, len(friends)+1):
    for perm in itertools.permutations(friends, r):
        current_time = start_time_minutes
        current_location = start_location
        itinerary = []
        valid = True
        for friend in perm:
            from_loc = current_location
            to_loc = friend['location']
            if (from_loc, to_loc) not in travel_times:
                valid = False
                break
            travel_time = travel_times[(from_loc, to_loc)]
            arrival_time = current_time + travel_time
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required']
            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - required
            if earliest_start > latest_start:
                valid = False
                break
            # add to itinerary
            start = earliest_start
            end = start + required
            itinerary.append({
                'name': friend['name'],
                'location': to_loc,
                'start': start,
                'end': end
            })
            current_time = end
            current_location = to_loc
        if valid:
            if len(itinerary) > max_length:
                max_length = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == max_length:
                # To handle ties, perhaps choose the one with earliest end time
                # But for simplicity, we'll just keep the first one found
                pass

# Now format best_itinerary into the required JSON structure
json_itinerary = []
for entry in best_itinerary:
    json_itinerary.append({
        "action": "meet",
        "location": entry['location'],
        "person": entry['name'],
        "start_time": minutes_to_time(entry['start']),
        "end_time": minutes_to_time(entry['end'])
    })

result = {
    "itinerary": json_itinerary
}

print(json.dumps(result, indent=2))
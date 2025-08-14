import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Emily',
        'location': 'Presidio',
        'available_start': 975,  # 16:15
        'available_end': 1260,   # 21:00
        'required_duration': 105
    },
    {
        'name': 'Joseph',
        'location': "Richmond District",
        'available_start': 1035, # 17:15
        'available_end': 1320,   # 22:00
        'required_duration': 120
    },
    {
        'name': 'Melissa',
        'location': 'Financial District',
        'available_start': 945,  # 15:45
        'available_end': 1305,   # 21:45
        'required_duration': 75
    }
]

travel_times = {
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
}

best_itinerary = None

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    previous_location = "Fisherman's Wharf"
    itinerary = []
    valid = True
    
    for friend in perm:
        from_location = previous_location
        to_location = friend['location']
        travel_duration = travel_times[(from_location, to_location)]
        arrival_time = current_time + travel_duration
        
        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + required
        
        if end_time > available_end:
            valid = False
            break
        
        itinerary.append({
            'action': 'meet',
            'location': to_location,
            'person': friend['name'],
            'start_time': to_time_str(start_time),
            'end_time': to_time_str(end_time)
        })
        
        current_time = end_time
        previous_location = to_location
    
    if valid:
        best_itinerary = itinerary
        break

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
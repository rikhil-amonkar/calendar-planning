import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

friends = [
    {
        'name': 'Rebecca',
        'location': 'Bayview',
        'available_start': 540,  # 9:00 AM
        'available_end': 765,    # 12:45 PM
        'required_duration': 90
    },
    {
        'name': 'Amanda',
        'location': 'Pacific Heights',
        'available_start': 18*60 + 30,  # 6:30 PM
        'available_end': 21*60 + 45,    # 9:45 PM
        'required_duration': 90
    },
    {
        'name': 'James',
        'location': 'Alamo Square',
        'available_start': 9*60 + 45,   # 9:45 AM
        'available_end': 21*60 + 15,    # 9:15 PM
        'required_duration': 90
    },
    {
        'name': 'Sarah',
        'location': 'Fisherman\'s Wharf',
        'available_start': 8*60 + 0,    # 8:00 AM
        'available_end': 21*60 + 30,    # 9:30 PM
        'required_duration': 90
    },
    {
        'name': 'Melissa',
        'location': 'Golden Gate Park',
        'available_start': 540,         # 9:00 AM
        'available_end': 18*60 + 45,    # 6:45 PM
        'required_duration': 90
    }
]

best_itinerary = []
best_count = 0

for perm in itertools.permutations(friends):
    current_time = 540  # Start at 9:00 AM
    current_location = 'The Castro'
    current_itinerary = []
    for friend in perm:
        origin = current_location
        destination = friend['location']
        travel_time = travel_times.get((origin, destination))
        if travel_time is None:
            break
        arrival_time = current_time + travel_time
        possible_start = max(arrival_time, friend['available_start'])
        required = friend['required_duration']
        if possible_start + required > friend['available_end']:
            break
        current_itinerary.append({
            'action': 'meet',
            'location': destination,
            'person': friend['name'],
            'start_time': possible_start,
            'end_time': possible_start + required
        })
        current_time = possible_start + required
        current_location = destination
    if len(current_itinerary) > best_count:
        best_count = len(current_itinerary)
        best_itinerary = current_itinerary

formatted_itinerary = []
for item in best_itinerary:
    formatted_itinerary.append({
        'action': 'meet',
        'location': item['location'],
        'person': item['person'],
        'start_time': minutes_to_time(item['start_time']),
        'end_time': minutes_to_time(item['end_time']),
    })

result = {
    "itinerary": formatted_itinerary
}

print(json.dumps(result, indent=2))
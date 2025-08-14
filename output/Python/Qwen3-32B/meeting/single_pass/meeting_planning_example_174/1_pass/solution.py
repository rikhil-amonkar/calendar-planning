import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Nob Hill': {'Pacific Heights': 8, 'Mission District': 13},
    'Pacific Heights': {'Nob Hill': 8, 'Mission District': 15},
    'Mission District': {'Nob Hill': 12, 'Pacific Heights': 16}
}

friends = [
    {
        'name': 'Kenneth',
        'location': 'Mission District',
        'available_start': 12 * 60,  # 720
        'available_end': 15 * 60 + 45,  # 945
        'min_duration': 45
    },
    {
        'name': 'Thomas',
        'location': 'Pacific Heights',
        'available_start': 15 * 60 + 30,  # 930
        'available_end': 19 * 60 + 15,  # 1155
        'min_duration': 75
    }
]

best_itinerary = []
max_friends = 0

start_time = 9 * 60  # 540
start_location = 'Nob Hill'

for order in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    valid = True
    for friend in order:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        start = max(arrival_time, friend['available_start'])
        if start + friend['min_duration'] > friend['available_end']:
            valid = False
            break
        end = start + friend['min_duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start,
            'end_time': end
        })
        current_time = end
        current_location = friend['location']
    if valid and len(itinerary) > max_friends:
        max_friends = len(itinerary)
        best_itinerary = itinerary

output = {"itinerary": []}
for meet in best_itinerary:
    output["itinerary"].append({
        "action": "meet",
        "location": meet['location'],
        "person": meet['person'],
        "start_time": to_time_str(meet['start_time']),
        "end_time": to_time_str(meet['end_time'])
    })

print(json.dumps(output, indent=2))
import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Emily',
        'location': 'Presidio',
        'available_start': 975,  # 4:15 PM
        'available_end': 1260,   # 9:00 PM
        'required_duration': 105
    },
    {
        'name': 'Joseph',
        'location': 'Richmond District',
        'available_start': 1035,  # 5:15 PM
        'available_end': 1320,    # 10:00 PM
        'required_duration': 120
    },
    {
        'name': 'Melissa',
        'location': 'Financial District',
        'available_start': 945,   # 3:45 PM
        'available_end': 1245,    # 9:45 PM
        'required_duration': 75
    }
]

travel_times = {
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Richmond District': 18,
        'Financial District': 11
    },
    'Presidio': {
        'Fisherman\'s Wharf': 19,
        'Richmond District': 7,
        'Financial District': 23
    },
    'Richmond District': {
        'Fisherman\'s Wharf': 18,
        'Presidio': 7,
        'Financial District': 22
    },
    'Financial District': {
        'Fisherman\'s Wharf': 10,
        'Presidio': 23,
        'Richmond District': 21
    }
}

best_solution = None
max_friends = 0

for length in [3, 2, 1]:
    for perm in itertools.permutations(friends, length):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Fisherman\'s Wharf'
        meetings = []
        feasible = True
        for friend in perm:
            next_location = friend['location']
            travel_time = travel_times[current_location][next_location]
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, friend['available_start'])
            required = friend['required_duration']
            end_time_candidate = start_time + required
            if end_time_candidate > friend['available_end']:
                feasible = False
                break
            meetings.append({
                'person': friend['name'],
                'location': next_location,
                'start_time': start_time,
                'end_time': end_time_candidate
            })
            current_time = end_time_candidate
            current_location = next_location
        if feasible:
            if len(meetings) > max_friends:
                max_friends = len(meetings)
                best_solution = meetings
            elif len(meetings) == max_friends:
                # For ties, we can keep the first one found
                pass
    if max_friends >= length:
        break

# Convert best_solution to the required JSON format
itinerary = []
for meeting in best_solution:
    itinerary.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['person'],
        "start_time": minutes_to_time_str(meeting['start_time']),
        "end_time": minutes_to_time_str(meeting['end_time'])
    })

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))
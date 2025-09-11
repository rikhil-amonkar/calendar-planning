import itertools
import json

travel_times = {
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Fisherman\'s Wharf': 25,
    },
    'Embarcadero': {
        'Bayview': 21,
        'Richmond District': 21,
        'Fisherman\'s Wharf': 6,
    },
    'Richmond District': {
        'Bayview': 26,
        'Embarcadero': 19,
        'Fisherman\'s Wharf': 18,
    },
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Embarcadero': 8,
        'Richmond District': 18,
    },
}

friends = [
    {
        'name': 'Jason',
        'location': "Fisherman's Wharf",
        'available_start': 16 * 60 + 0,  # 960
        'available_end': 16 * 60 + 45,   # 1005
        'required_duration': 30,
    },
    {
        'name': 'Jessica',
        'location': 'Embarcadero',
        'available_start': 16 * 60 + 45,  # 1005
        'available_end': 19 * 60 + 0,     # 1140
        'required_duration': 30,
    },
    {
        'name': 'Sandra',
        'location': 'Richmond District',
        'available_start': 18 * 60 + 30,  # 1110
        'available_end': 21 * 60 + 45,    # 1265
        'required_duration': 120,
    }
]

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

best_itinerary = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Bayview'
    itinerary = []
    valid = True

    for friend in perm:
        destination = friend['location']
        if current_location not in travel_times or destination not in travel_times[current_location]:
            valid = False
            break
        travel_time_min = travel_times[current_location][destination]
        arrival_time = current_time + travel_time_min

        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required_duration']

        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required

        if earliest_start > latest_start:
            valid = False
            break

        start_time = earliest_start
        end_time = start_time + required

        itinerary.append({
            'action': 'meet',
            'location': destination,
            'person': friend['name'],
            'start_time': start_time,
            'end_time': end_time,
        })

        current_time = end_time
        current_location = destination

    if valid and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

result = {
    "itinerary": []
}

for entry in best_itinerary:
    result["itinerary"].append({
        "action": "meet",
        "location": entry['location'],
        "person": entry['person'],
        "start_time": minutes_to_time_str(entry['start_time']),
        "end_time": minutes_to_time_str(entry['end_time']),
    })

print(json.dumps(result, indent=2))
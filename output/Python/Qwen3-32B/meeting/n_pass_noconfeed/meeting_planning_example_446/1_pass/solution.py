import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'available_start': 570,  # 9:30 AM
        'available_end': 810,    # 1:30 PM
        'required_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'available_start': 735,  # 12:15 PM
        'available_end': 1715,   # 8:15 PM
        'required_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'available_start': 795,  # 1:15 PM
        'available_end': 1005,   # 4:45 PM
        'required_duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'available_start': 795,  # 1:15 PM
        'available_end': 1005,   # 4:45 PM
        'required_duration': 75
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'available_start': 1170,  # 7:30 PM
        'available_end': 1275,    # 9:15 PM
        'required_duration': 75
    }
]

travel_times = {
    'Richmond District': {
        'Marina District': 9,
        'Chinatown': 20,
        'Financial District': 22,
        'Bayview': 26,
        'Union Square': 21
    },
    'Marina District': {
        'Richmond District': 11,
        'Chinatown': 16,
        'Financial District': 17,
        'Bayview': 27,
        'Union Square': 16
    },
    'Chinatown': {
        'Richmond District': 20,
        'Marina District': 12,
        'Financial District': 5,
        'Bayview': 22,
        'Union Square': 7
    },
    'Financial District': {
        'Richmond District': 21,
        'Marina District': 15,
        'Chinatown': 5,
        'Bayview': 19,
        'Union Square': 9
    },
    'Bayview': {
        'Richmond District': 25,
        'Marina District': 25,
        'Chinatown': 18,
        'Financial District': 19,
        'Union Square': 17
    },
    'Union Square': {
        'Richmond District': 20,
        'Marina District': 18,
        'Chinatown': 7,
        'Financial District': 9,
        'Bayview': 15
    }
}

best_itinerary = None

for length in range(5, 0, -1):
    for perm in itertools.permutations(friends, length):
        current_time = 540  # 9:00 AM
        current_location = 'Richmond District'
        itinerary = []
        valid = True

        for friend in perm:
            loc = friend['location']
            available_start = friend['available_start']
            available_end = friend['available_end']
            duration = friend['required_duration']

            # Check if travel time exists
            if current_location not in travel_times or loc not in travel_times[current_location]:
                valid = False
                break
            travel_time = travel_times[current_location][loc]

            arrival_time = current_time + travel_time

            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - duration

            if earliest_start > latest_start:
                valid = False
                break

            # Schedule meeting
            start_meet = earliest_start
            end_meet = start_meet + duration
            itinerary.append( (friend, start_meet, end_meet) )

            current_time = end_meet
            current_location = loc

        if valid:
            best_itinerary = itinerary
            break
    if best_itinerary:
        break

# Convert best itinerary to JSON format
itinerary_json = []
for entry in best_itinerary:
    friend, start, end = entry
    start_str = minutes_to_time_str(start)
    end_str = minutes_to_time_str(end)
    itinerary_json.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_str,
        "end_time": end_str
    })

print(json.dumps({"itinerary": itinerary_json}, indent=2))
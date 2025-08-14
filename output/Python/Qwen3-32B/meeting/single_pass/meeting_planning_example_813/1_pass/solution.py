import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_feasible(perm, travel_times):
    current_location = 'Marina District'
    current_time = 540  # 9:00 AM in minutes
    for friend in perm:
        loc = friend['location']
        available_start = friend['available_start']
        available_end = friend['available_end']
        duration = friend['required_duration']
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time
        meeting_end_time = arrival_time + duration
        if arrival_time < available_start or meeting_end_time > available_end:
            return False
        current_time = meeting_end_time
        current_location = loc
    return True

friends = [
    {
        'name': 'Joshua',
        'location': 'Embarcadero',
        'available_start': 585,
        'available_end': 1080,
        'required_duration': 105
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'available_start': 585,
        'available_end': 1215,
        'required_duration': 75
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'available_start': 645,
        'available_end': 1215,
        'required_duration': 120
    },
    {
        'name': 'Joseph',
        'location': 'Chinatown',
        'available_start': 420,
        'available_end': 930,
        'required_duration': 60
    },
    {
        'name': 'Matthew',
        'location': 'Golden Gate Park',
        'available_start': 660,
        'available_end': 1170,
        'required_duration': 45
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'available_start': 645,
        'available_end': 675,
        'required_duration': 15
    },
    {
        'name': 'Paul',
        'location': 'Haight-Ashbury',
        'available_start': 1155,
        'available_end': 1230,
        'required_duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'available_start': 1020,
        'available_end': 1305,
        'required_duration': 45
    }
]

travel_times = {
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Union Square': 16,
        'Chinatown': 15,
        'Golden Gate Park': 18,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Union Square': 10,
        'Chinatown': 7,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'Haight-Ashbury': 21,
        'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27,
        'Embarcadero': 19,
        'Union Square': 18,
        'Chinatown': 19,
        'Golden Gate Park': 22,
        'Financial District': 19,
        'Haight-Ashbury': 19,
        'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18,
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Golden Gate Park': 22,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 12,
        'Embarcadero': 5,
        'Bayview': 20,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Financial District': 5,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Embarcadero': 25,
        'Bayview': 23,
        'Union Square': 22,
        'Chinatown': 23,
        'Financial District': 26,
        'Haight-Ashbury': 7,
        'Mission District': 17
    },
    'Financial District': {
        'Marina District': 15,
        'Embarcadero': 4,
        'Bayview': 19,
        'Union Square': 9,
        'Chinatown': 5,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Embarcadero': 20,
        'Bayview': 18,
        'Union Square': 19,
        'Chinatown': 19,
        'Golden Gate Park': 7,
        'Financial District': 21,
        'Mission District': 11
    },
    'Mission District': {
        'Marina District': 19,
        'Embarcadero': 19,
        'Bayview': 14,
        'Union Square': 15,
        'Chinatown': 16,
        'Golden Gate Park': 17,
        'Financial District': 15,
        'Haight-Ashbury': 12
    }
}

best_sequence = None
best_length = 0
best_end_time = float('inf')

for r in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, r):
        if is_feasible(perm, travel_times):
            current_location = 'Marina District'
            current_time = 540
            for friend in perm:
                loc = friend['location']
                travel_time = travel_times[current_location][loc]
                arrival_time = current_time + travel_time
                duration = friend['required_duration']
                current_time = arrival_time + duration
                current_location = loc
            if len(perm) > best_length or (len(perm) == best_length and current_time < best_end_time):
                best_sequence = perm
                best_length = len(perm)
                best_end_time = current_time

if best_sequence:
    itinerary = []
    current_location = 'Marina District'
    current_time = 540
    for friend in best_sequence:
        loc = friend['location']
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time
        duration = friend['required_duration']
        end_time = arrival_time + duration
        itinerary.append({
            'action': 'meet',
            'location': loc,
            'person': friend['name'],
            'start_time': to_time_str(arrival_time),
            'end_time': to_time_str(end_time)
        })
        current_time = end_time
        current_location = loc
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))
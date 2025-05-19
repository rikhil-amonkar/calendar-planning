import itertools
import json

friends = [
    {
        'name': 'Karen',
        'location': 'Haight-Ashbury',
        'start': 21 * 60,
        'end': 21 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'start': 13 * 60 + 45,
        'end': 21 * 60,
        'duration': 90
    },
    {
        'name': 'Brian',
        'location': 'Russian Hill',
        'start': 15 * 60 + 30,
        'end': 21 * 60 + 45,
        'duration': 60
    },
    {
        'name': 'Kenneth',
        'location': 'North Beach',
        'start': 9 * 60 + 45,
        'end': 21 * 60,
        'duration': 30
    },
    {
        'name': 'Jason',
        'location': 'Chinatown',
        'start': 8 * 60 + 15,
        'end': 11 * 60 + 45,
        'duration': 75
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'start': 14 * 60 + 45,
        'end': 18 * 60 + 45,
        'duration': 105
    },
    {
        'name': 'Kimberly',
        'location': 'Embarcadero',
        'start': 9 * 60 + 45,
        'end': 19 * 60 + 30,
        'duration': 75
    },
    {
        'name': 'Steven',
        'location': 'Financial District',
        'start': 7 * 60 + 15,
        'end': 21 * 60 + 15,
        'duration': 60
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'start': 10 * 60 + 15,
        'end': 13 * 60,
        'duration': 75
    }
]

travel_times = {
    'Presidio': {
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Russian Hill': 14,
        'North Beach': 18,
        'Chinatown': 21,
        'Union Square': 22,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Presidio': 15,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'North Beach': 19,
        'Chinatown': 19,
        'Union Square': 19,
        'Embarcadero': 20,
        'Financial District': 21,
        'Marina District': 17
    },
    'Nob Hill': {
        'Presidio': 17,
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'North Beach': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 9,
        'Financial District': 9,
        'Marina District': 11
    },
    'Russian Hill': {
        'Presidio': 14,
        'Haight-Ashbury': 17,
        'Nob Hill': 5,
        'North Beach': 5,
        'Chinatown': 9,
        'Union Square': 10,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7
    },
    'North Beach': {
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Russian Hill': 4,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9
    },
    'Chinatown': {
        'Presidio': 19,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Russian Hill': 7,
        'North Beach': 3,
        'Union Square': 7,
        'Embarcadero': 5,
        'Financial District': 5,
        'Marina District': 12
    },
    'Union Square': {
        'Presidio': 24,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Russian Hill': 13,
        'North Beach': 10,
        'Chinatown': 7,
        'Embarcadero': 11,
        'Financial District': 9,
        'Marina District': 18
    },
    'Embarcadero': {
        'Presidio': 20,
        'Haight-Ashbury': 21,
        'Nob Hill': 10,
        'Russian Hill': 8,
        'North Beach': 5,
        'Chinatown': 7,
        'Union Square': 10,
        'Financial District': 5,
        'Marina District': 12
    },
    'Financial District': {
        'Presidio': 22,
        'Haight-Ashbury': 19,
        'Nob Hill': 8,
        'Russian Hill': 11,
        'North Beach': 7,
        'Chinatown': 5,
        'Union Square': 9,
        'Embarcadero': 4,
        'Marina District': 15
    },
    'Marina District': {
        'Presidio': 10,
        'Haight-Ashbury': 16,
        'Nob Hill': 12,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Union Square': 16,
        'Embarcadero': 14,
        'Financial District': 17
    }
}

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

best_count = 0
best_itinerary = []
best_end_time = float('inf')

for perm in itertools.permutations(friends):
    current_location = 'Presidio'
    current_time = 540
    itinerary = []
    count = 0
    valid = True
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        try:
            travel_time = travel_times[from_loc][to_loc]
        except KeyError:
            valid = False
            break
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + friend['duration']
        if end_time > friend['end']:
            valid = False
            break
        itinerary.append({
            "action": "meet",
            "location": to_loc,
            "person": friend['name'],
            "start_time": time_to_str(start_time),
            "end_time": time_to_str(end_time)
        })
        current_time = end_time
        current_location = to_loc
        count += 1
    if valid:
        if count > best_count or (count == best_count and current_time < best_end_time):
            best_count = count
            best_end_time = current_time
            best_itinerary = itinerary.copy()

print(json.dumps({"itinerary": best_itinerary}, indent=2))
import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'available_start': 465,
        'available_end': 1050,
        'duration': 120
    },
    {
        'name': 'David',
        'location': 'Sunset District',
        'available_start': 750,
        'available_end': 1185,
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Alamo Square',
        'available_start': 525,
        'available_end': 825,
        'duration': 90
    },
    {
        'name': 'Jessica',
        'location': 'Financial District',
        'available_start': 570,
        'available_end': 1125,
        'duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'available_start': 435,
        'available_end': 1005,
        'duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'available_start': 915,
        'available_end': 1020,
        'duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'Presidio',
        'available_start': 1140,
        'available_end': 1185,
        'duration': 45
    },
    {
        'name': 'Karen',
        'location': 'Golden Gate Park',
        'available_start': 1170,
        'available_end': 1320,
        'duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Bayview',
        'available_start': 1275,
        'available_end': 1335,
        'duration': 15
    }
]

travel_time = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27,
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20,
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22,
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16,
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19,
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25,
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21,
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31,
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 22,
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22,
    },
}

start_time_minutes = 540  # 9:00 AM
start_location = 'Richmond District'

for subset_size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        for perm in itertools.permutations(subset):
            current_time = start_time_minutes
            current_location = start_location
            valid = True
            itinerary = []
            for friend in perm:
                try:
                    travel_duration = travel_time[current_location][friend['location']]
                except KeyError:
                    valid = False
                    break
                arrival_time = current_time + travel_duration
                available_start = friend['available_start']
                available_end = friend['available_end']
                duration = friend['duration']
                if arrival_time > available_end - duration:
                    valid = False
                    break
                meeting_start = max(arrival_time, available_start)
                meeting_end = meeting_start + duration
                if meeting_end > available_end:
                    valid = False
                    break
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': format_time(meeting_start),
                    'end_time': format_time(meeting_end)
                })
                current_time = meeting_end
                current_location = friend['location']
            if valid:
                print(json.dumps({"itinerary": itinerary}, indent=2))
                exit()

print(json.dumps({"itinerary": []}))
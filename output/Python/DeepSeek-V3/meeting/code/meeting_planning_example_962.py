import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'The Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17
    },
    'Marina District': {
        'The Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19
    },
    'Presidio': {
        'The Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15
    },
    'North Beach': {
        'The Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27
    },
    'Embarcadero': {
        'The Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10
    },
    'Richmond District': {
        'The Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11
    },
    'Alamo Square': {
        'The Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16
    },
    'Financial District': {
        'The Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30
    },
    'Sunset District': {
        'The Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30
    }
}

friends = [
    {'name': 'Elizabeth', 'location': 'Marina District', 'start': '19:00', 'end': '20:45', 'duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'start': '8:30', 'end': '13:15', 'duration': 105},
    {'name': 'Timothy', 'location': 'North Beach', 'start': '19:45', 'end': '22:00', 'duration': 90},
    {'name': 'David', 'location': 'Embarcadero', 'start': '10:45', 'end': '12:30', 'duration': 30},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': '16:45', 'end': '21:30', 'duration': 75},
    {'name': 'Lisa', 'location': 'Golden Gate Park', 'start': '17:30', 'end': '21:45', 'duration': 45},
    {'name': 'Ronald', 'location': 'Richmond District', 'start': '8:00', 'end': '9:30', 'duration': 90},
    {'name': 'Stephanie', 'location': 'Alamo Square', 'start': '15:30', 'end': '16:30', 'duration': 30},
    {'name': 'Helen', 'location': 'Financial District', 'start': '17:30', 'end': '18:30', 'duration': 45},
    {'name': 'Laura', 'location': 'Sunset District', 'start': '17:45', 'end': '21:15', 'duration': 90}
]

# Filter friends that can be met based on duration
valid_friends = [f for f in friends if time_to_minutes(f['end']) - time_to_minutes(f['start']) >= f['duration']]

# Prioritize friends with tighter time windows
valid_friends.sort(key=lambda x: time_to_minutes(x['end']) - time_to_minutes(x['start']))

current_time = time_to_minutes('9:00')
current_location = 'The Castro'
itinerary = []

# Try to meet Ronald first (earliest)
ronald = next(f for f in valid_friends if f['name'] == 'Ronald')
travel_time = travel_times[current_location][ronald['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(ronald['end']) - ronald['duration']:
    start_time = max(arrival_time, time_to_minutes(ronald['start']))
    end_time = start_time + ronald['duration']
    itinerary.append({
        'action': 'meet',
        'location': ronald['location'],
        'person': ronald['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = ronald['location']
    valid_friends.remove(ronald)

# Next try Joshua
joshua = next(f for f in valid_friends if f['name'] == 'Joshua')
travel_time = travel_times[current_location][joshua['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(joshua['end']) - joshua['duration']:
    start_time = max(arrival_time, time_to_minutes(joshua['start']))
    end_time = start_time + joshua['duration']
    itinerary.append({
        'action': 'meet',
        'location': joshua['location'],
        'person': joshua['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = joshua['location']
    valid_friends.remove(joshua)

# Next try David
david = next(f for f in valid_friends if f['name'] == 'David')
travel_time = travel_times[current_location][david['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(david['end']) - david['duration']:
    start_time = max(arrival_time, time_to_minutes(david['start']))
    end_time = start_time + david['duration']
    itinerary.append({
        'action': 'meet',
        'location': david['location'],
        'person': david['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = david['location']
    valid_friends.remove(david)

# Next try Stephanie
stephanie = next(f for f in valid_friends if f['name'] == 'Stephanie')
travel_time = travel_times[current_location][stephanie['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(stephanie['end']) - stephanie['duration']:
    start_time = max(arrival_time, time_to_minutes(stephanie['start']))
    end_time = start_time + stephanie['duration']
    itinerary.append({
        'action': 'meet',
        'location': stephanie['location'],
        'person': stephanie['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = stephanie['location']
    valid_friends.remove(stephanie)

# Next try Helen
helen = next(f for f in valid_friends if f['name'] == 'Helen')
travel_time = travel_times[current_location][helen['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(helen['end']) - helen['duration']:
    start_time = max(arrival_time, time_to_minutes(helen['start']))
    end_time = start_time + helen['duration']
    itinerary.append({
        'action': 'meet',
        'location': helen['location'],
        'person': helen['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = helen['location']
    valid_friends.remove(helen)

# Next try Kimberly
kimberly = next(f for f in valid_friends if f['name'] == 'Kimberly')
travel_time = travel_times[current_location][kimberly['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(kimberly['end']) - kimberly['duration']:
    start_time = max(arrival_time, time_to_minutes(kimberly['start']))
    end_time = start_time + kimberly['duration']
    itinerary.append({
        'action': 'meet',
        'location': kimberly['location'],
        'person': kimberly['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = kimberly['location']
    valid_friends.remove(kimberly)

# Next try Lisa
lisa = next(f for f in valid_friends if f['name'] == 'Lisa')
travel_time = travel_times[current_location][lisa['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(lisa['end']) - lisa['duration']:
    start_time = max(arrival_time, time_to_minutes(lisa['start']))
    end_time = start_time + lisa['duration']
    itinerary.append({
        'action': 'meet',
        'location': lisa['location'],
        'person': lisa['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = lisa['location']
    valid_friends.remove(lisa)

# Next try Laura
laura = next(f for f in valid_friends if f['name'] == 'Laura')
travel_time = travel_times[current_location][laura['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(laura['end']) - laura['duration']:
    start_time = max(arrival_time, time_to_minutes(laura['start']))
    end_time = start_time + laura['duration']
    itinerary.append({
        'action': 'meet',
        'location': laura['location'],
        'person': laura['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = laura['location']
    valid_friends.remove(laura)

# Finally try Elizabeth and Timothy (late evening)
elizabeth = next(f for f in valid_friends if f['name'] == 'Elizabeth')
travel_time = travel_times[current_location][elizabeth['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(elizabeth['end']) - elizabeth['duration']:
    start_time = max(arrival_time, time_to_minutes(elizabeth['start']))
    end_time = start_time + elizabeth['duration']
    itinerary.append({
        'action': 'meet',
        'location': elizabeth['location'],
        'person': elizabeth['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    current_time = end_time
    current_location = elizabeth['location']
    valid_friends.remove(elizabeth)

timothy = next(f for f in valid_friends if f['name'] == 'Timothy')
travel_time = travel_times[current_location][timothy['location']]
arrival_time = current_time + travel_time
if arrival_time <= time_to_minutes(timothy['end']) - timothy['duration']:
    start_time = max(arrival_time, time_to_minutes(timothy['start']))
    end_time = start_time + timothy['duration']
    itinerary.append({
        'action': 'meet',
        'location': timothy['location'],
        'person': timothy['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })

print(json.dumps({'itinerary': itinerary}, indent=2))
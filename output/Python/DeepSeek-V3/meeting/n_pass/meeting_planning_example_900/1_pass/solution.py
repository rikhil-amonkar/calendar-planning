import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data
travel_times = {
    'Richmond District': {
        'The Castro': 16, 'Nob Hill': 17, 'Marina District': 9, 'Pacific Heights': 10,
        'Haight-Ashbury': 10, 'Mission District': 20, 'Chinatown': 20, 'Russian Hill': 13,
        'Alamo Square': 13, 'Bayview': 27
    },
    'The Castro': {
        'Richmond District': 16, 'Nob Hill': 16, 'Marina District': 21, 'Pacific Heights': 16,
        'Haight-Ashbury': 6, 'Mission District': 7, 'Chinatown': 22, 'Russian Hill': 18,
        'Alamo Square': 8, 'Bayview': 19
    },
    'Nob Hill': {
        'Richmond District': 14, 'The Castro': 17, 'Marina District': 11, 'Pacific Heights': 8,
        'Haight-Ashbury': 13, 'Mission District': 13, 'Chinatown': 6, 'Russian Hill': 5,
        'Alamo Square': 11, 'Bayview': 19
    },
    'Marina District': {
        'Richmond District': 11, 'The Castro': 22, 'Nob Hill': 12, 'Pacific Heights': 7,
        'Haight-Ashbury': 16, 'Mission District': 20, 'Chinatown': 15, 'Russian Hill': 8,
        'Alamo Square': 15, 'Bayview': 27
    },
    'Pacific Heights': {
        'Richmond District': 12, 'The Castro': 16, 'Nob Hill': 8, 'Marina District': 6,
        'Haight-Ashbury': 11, 'Mission District': 15, 'Chinatown': 11, 'Russian Hill': 7,
        'Alamo Square': 10, 'Bayview': 22
    },
    'Haight-Ashbury': {
        'Richmond District': 10, 'The Castro': 6, 'Nob Hill': 15, 'Marina District': 17,
        'Pacific Heights': 12, 'Mission District': 11, 'Chinatown': 19, 'Russian Hill': 17,
        'Alamo Square': 5, 'Bayview': 18
    },
    'Mission District': {
        'Richmond District': 20, 'The Castro': 7, 'Nob Hill': 12, 'Marina District': 19,
        'Pacific Heights': 16, 'Haight-Ashbury': 12, 'Chinatown': 16, 'Russian Hill': 15,
        'Alamo Square': 11, 'Bayview': 14
    },
    'Chinatown': {
        'Richmond District': 20, 'The Castro': 22, 'Nob Hill': 9, 'Marina District': 12,
        'Pacific Heights': 10, 'Haight-Ashbury': 19, 'Mission District': 17, 'Russian Hill': 7,
        'Alamo Square': 17, 'Bayview': 20
    },
    'Russian Hill': {
        'Richmond District': 14, 'The Castro': 21, 'Nob Hill': 5, 'Marina District': 7,
        'Pacific Heights': 7, 'Haight-Ashbury': 17, 'Mission District': 16, 'Chinatown': 9,
        'Alamo Square': 15, 'Bayview': 23
    },
    'Alamo Square': {
        'Richmond District': 11, 'The Castro': 8, 'Nob Hill': 11, 'Marina District': 15,
        'Pacific Heights': 10, 'Haight-Ashbury': 5, 'Mission District': 10, 'Chinatown': 15,
        'Russian Hill': 13, 'Bayview': 16
    },
    'Bayview': {
        'Richmond District': 25, 'The Castro': 19, 'Nob Hill': 20, 'Marina District': 27,
        'Pacific Heights': 23, 'Haight-Ashbury': 19, 'Mission District': 13, 'Chinatown': 19,
        'Russian Hill': 23, 'Alamo Square': 16
    }
}

friends = [
    {'name': 'Matthew', 'location': 'The Castro', 'start': '16:30', 'end': '20:00', 'duration': 45},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': '15:15', 'end': '19:15', 'duration': 105},
    {'name': 'Brian', 'location': 'Marina District', 'start': '14:15', 'end': '22:00', 'duration': 30},
    {'name': 'Emily', 'location': 'Pacific Heights', 'start': '11:15', 'end': '19:45', 'duration': 15},
    {'name': 'Karen', 'location': 'Haight-Ashbury', 'start': '11:45', 'end': '17:30', 'duration': 30},
    {'name': 'Stephanie', 'location': 'Mission District', 'start': '13:00', 'end': '15:45', 'duration': 75},
    {'name': 'James', 'location': 'Chinatown', 'start': '14:30', 'end': '19:00', 'duration': 120},
    {'name': 'Steven', 'location': 'Russian Hill', 'start': '14:00', 'end': '20:00', 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': '13:00', 'end': '17:15', 'duration': 120},
    {'name': 'William', 'location': 'Bayview', 'start': '18:15', 'end': '20:15', 'duration': 90}
]

current_location = 'Richmond District'
current_time = time_to_minutes('9:00')

def is_valid_schedule(schedule):
    global current_location, current_time
    loc = current_location
    time = current_time
    for meet in schedule:
        travel_time = travel_times[loc][meet['location']]
        arrival_time = time + travel_time
        start_time = max(arrival_time, time_to_minutes(meet['start']))
        end_time = start_time + meet['duration']
        if end_time > time_to_minutes(meet['end']):
            return False
        loc = meet['location']
        time = end_time
    return True

def calculate_schedule_time(schedule):
    global current_location, current_time
    loc = current_location
    time = current_time
    total_meetings = 0
    for meet in schedule:
        travel_time = travel_times[loc][meet['location']]
        arrival_time = time + travel_time
        start_time = max(arrival_time, time_to_minutes(meet['start']))
        end_time = start_time + meet['duration']
        if end_time > time_to_minutes(meet['end']):
            return -1
        loc = meet['location']
        time = end_time
        total_meetings += 1
    return total_meetings

best_schedule = None
best_count = 0

# We'll try permutations of all friends, but limit to a reasonable number for performance
for perm in permutations(friends, min(5, len(friends))):
    if calculate_schedule_time(perm) > best_count:
        best_count = calculate_schedule_time(perm)
        best_schedule = perm
    if best_count == len(friends):
        break

# Now try to find a schedule that includes all mandatory meetings (like William at Bayview)
mandatory = [f for f in friends if f['name'] in ['William', 'Elizabeth', 'James']]
optional = [f for f in friends if f['name'] not in ['William', 'Elizabeth', 'James']]

for m in mandatory:
    for o in optional:
        test_schedule = [m, o]
        if is_valid_schedule(test_schedule) and len(test_schedule) > best_count:
            best_count = len(test_schedule)
            best_schedule = test_schedule

# Generate itinerary
itinerary = []
if best_schedule:
    loc = current_location
    time = current_time
    for meet in best_schedule:
        travel_time = travel_times[loc][meet['location']]
        arrival_time = time + travel_time
        start_time = max(arrival_time, time_to_minutes(meet['start']))
        end_time = start_time + meet['duration']
        itinerary.append({
            'action': 'meet',
            'location': meet['location'],
            'person': meet['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        loc = meet['location']
        time = end_time

output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))
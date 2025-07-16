import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 9,
        'Union Square': 7,
        'Golden Gate Park': 22
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22
    }
}

friends = {
    'Karen': {
        'location': 'Russian Hill',
        'start': time_to_minutes('20:45'),
        'end': time_to_minutes('21:45'),
        'duration': 60
    },
    'Jessica': {
        'location': 'The Castro',
        'start': time_to_minutes('15:45'),
        'end': time_to_minutes('19:30'),
        'duration': 60
    },
    'Matthew': {
        'location': 'Richmond District',
        'start': time_to_minutes('7:30'),
        'end': time_to_minutes('15:15'),
        'duration': 15
    },
    'Michelle': {
        'location': 'Marina District',
        'start': time_to_minutes('10:30'),
        'end': time_to_minutes('18:45'),
        'duration': 75
    },
    'Carol': {
        'location': 'North Beach',
        'start': time_to_minutes('12:00'),
        'end': time_to_minutes('17:00'),
        'duration': 90
    },
    'Stephanie': {
        'location': 'Union Square',
        'start': time_to_minutes('10:45'),
        'end': time_to_minutes('14:15'),
        'duration': 30
    },
    'Linda': {
        'location': 'Golden Gate Park',
        'start': time_to_minutes('10:45'),
        'end': time_to_minutes('22:00'),
        'duration': 90
    }
}

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

def calculate_schedule(permutation):
    schedule = []
    loc = current_location
    time = current_time
    for friend_name in permutation:
        friend = friends[friend_name]
        travel_time = travel_times[loc][friend['location']]
        arrival_time = time + travel_time
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + friend['duration']
        if end_time > friend['end']:
            return None
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend_name,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        loc = friend['location']
        time = end_time
    return schedule

best_schedule = None
max_friends = 0

for perm in permutations(friends.keys()):
    schedule = calculate_schedule(perm)
    if schedule and len(schedule) > max_friends:
        best_schedule = schedule
        max_friends = len(schedule)
    elif schedule and len(schedule) == max_friends:
        if best_schedule is None or schedule[-1]['end_time'] < best_schedule[-1]['end_time']:
            best_schedule = schedule

if best_schedule is None:
    print(json.dumps({"itinerary": []}))
else:
    print(json.dumps({"itinerary": best_schedule}, indent=2))
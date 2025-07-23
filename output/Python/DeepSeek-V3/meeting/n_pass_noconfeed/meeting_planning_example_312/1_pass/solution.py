import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
travel_times = {
    'Richmond District': {
        'Sunset District': 11,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Richmond District': 12,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11
    },
    'Haight-Ashbury': {
        'Richmond District': 10,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Richmond District': 20,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17
    }
}

friends = {
    'Sarah': {
        'location': 'Sunset District',
        'available_start': '10:45',
        'available_end': '19:00',
        'duration': 30
    },
    'Richard': {
        'location': 'Haight-Ashbury',
        'available_start': '11:45',
        'available_end': '15:45',
        'duration': 90
    },
    'Elizabeth': {
        'location': 'Mission District',
        'available_start': '11:00',
        'available_end': '17:15',
        'duration': 120
    },
    'Michelle': {
        'location': 'Golden Gate Park',
        'available_start': '18:15',
        'available_end': '20:45',
        'duration': 90
    }
}

current_location = 'Richmond District'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for friend in order:
        data = friends[friend]
        dest = data['location']
        travel_time = travel_times[loc][dest]
        arrival_time = time + travel_time
        
        available_start = time_to_minutes(data['available_start'])
        available_end = time_to_minutes(data['available_end'])
        duration = data['duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time > available_end:
            return None
        
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        loc = dest
        time = end_time
    
    return schedule

best_schedule = None
max_friends = 0

# Try all possible orders of meeting friends
for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    if schedule is not None and len(schedule) >= max_friends:
        if len(schedule) > max_friends or (best_schedule is None or schedule[-1]['end_time'] < best_schedule[-1]['end_time']):
            best_schedule = schedule
            max_friends = len(schedule)

if best_schedule is None:
    print(json.dumps({"itinerary": []}))
else:
    print(json.dumps({"itinerary": best_schedule}, indent=2))
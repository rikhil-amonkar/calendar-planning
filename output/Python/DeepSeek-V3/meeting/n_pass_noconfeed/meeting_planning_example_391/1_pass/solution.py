import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Financial District': 30
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Presidio': 18,
        'Financial District': 17
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Presidio': 14,
        'Financial District': 11
    },
    'Presidio': {
        'Sunset District': 15,
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Financial District': 23
    },
    'Financial District': {
        'Sunset District': 31,
        'Alamo Square': 17,
        'Russian Hill': 10,
        'Presidio': 22
    }
}

friends = {
    'Kevin': {
        'location': 'Alamo Square',
        'available_start': '8:15',
        'available_end': '21:30',
        'duration': 75
    },
    'Kimberly': {
        'location': 'Russian Hill',
        'available_start': '8:45',
        'available_end': '12:30',
        'duration': 30
    },
    'Joseph': {
        'location': 'Presidio',
        'available_start': '18:30',
        'available_end': '19:15',
        'duration': 45
    },
    'Thomas': {
        'location': 'Financial District',
        'available_start': '19:00',
        'available_end': '21:45',
        'duration': 45
    }
}

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    for friend in order:
        info = friends[friend]
        dest = info['location']
        travel_time = travel_times[loc][dest]
        arrival_time = time + travel_time
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        duration = info['duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time > available_end:
            return None
        
        schedule.append({
            'friend': friend,
            'location': dest,
            'start_time': start_time,
            'end_time': end_time,
            'travel_time': travel_time
        })
        
        loc = dest
        time = end_time
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    return len(schedule)

best_schedule = None
best_score = -1

# Generate all possible orders of meeting friends
for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

if best_schedule:
    itinerary = []
    for event in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": event['location'],
            "person": event['friend'],
            "start_time": minutes_to_time(event['start_time']),
            "end_time": minutes_to_time(event['end_time'])
        })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))
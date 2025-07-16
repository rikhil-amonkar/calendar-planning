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
    'Sunset District': {
        'Russian Hill': 24,
        'Chinatown': 30,
        'Presidio': 16,
        'Fisherman\'s Wharf': 29
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Fisherman\'s Wharf': 7
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'Presidio': 19,
        'Fisherman\'s Wharf': 8
    },
    'Presidio': {
        'Sunset District': 15,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Fisherman\'s Wharf': 19
    },
    'Fisherman\'s Wharf': {
        'Sunset District': 27,
        'Russian Hill': 7,
        'Chinatown': 12,
        'Presidio': 17
    }
}

friends = {
    'William': {
        'location': 'Russian Hill',
        'available_start': '18:30',
        'available_end': '20:45',
        'min_duration': 105
    },
    'Michelle': {
        'location': 'Chinatown',
        'available_start': '8:15',
        'available_end': '14:00',
        'min_duration': 15
    },
    'George': {
        'location': 'Presidio',
        'available_start': '10:30',
        'available_end': '18:45',
        'min_duration': 30
    },
    'Robert': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:00',
        'available_end': '13:45',
        'min_duration': 30
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
        travel = travel_times[loc][dest]
        arrival = time + travel
        start = max(arrival, time_to_minutes(info['available_start']))
        end = min(start + info['min_duration'], time_to_minutes(info['available_end']))
        
        if end <= start:
            return None
        
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })
        
        loc = dest
        time = end
    
    return schedule

best_schedule = None
best_count = 0

for perm in permutations(friends.keys()):
    schedule = calculate_schedule(perm)
    if schedule and len(schedule) > best_count:
        best_schedule = schedule
        best_count = len(schedule)

if best_schedule:
    result = {"itinerary": best_schedule}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))
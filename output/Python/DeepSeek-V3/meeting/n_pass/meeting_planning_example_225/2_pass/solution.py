import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Input parameters
travel_times = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
}

friends = {
    'Sarah': {
        'location': 'North Beach',
        'available_start': '16:00',
        'available_end': '18:15',
        'min_duration': 60
    },
    'Jeffrey': {
        'location': 'Union Square',
        'available_start': '15:00',
        'available_end': '22:00',
        'min_duration': 75
    },
    'Brian': {
        'location': 'Alamo Square',
        'available_start': '16:00',
        'available_end': '17:30',
        'min_duration': 75
    }
}

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    met_friends = set()
    
    for friend in order:
        if friend in met_friends:
            continue
        info = friends[friend]
        dest = info['location']
        travel_time = travel_times[(loc, dest)]
        arrival_time = time + travel_time
        
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        min_duration = info['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            continue
        
        schedule.append({
            'friend': friend,
            'location': dest,
            'start_time': start_time,
            'end_time': end_time,
            'travel_time': travel_time
        })
        
        met_friends.add(friend)
        loc = dest
        time = end_time
    
    return met_friends, schedule

best_met = set()
best_schedule = []

# Try all possible orders to find the best schedule
for perm in permutations(friends.keys()):
    met, schedule = calculate_schedule(perm)
    if len(met) > len(best_met) or (len(met) == len(best_met) and schedule[-1]['end_time'] < best_schedule[-1]['end_time'] if best_schedule else False):
        best_met = met
        best_schedule = schedule

itinerary = []
for event in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": event['location'],
        "person": event['friend'],
        "start_time": minutes_to_time(event['start_time']),
        "end_time": minutes_to_time(event['end_time'])
    })

result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))
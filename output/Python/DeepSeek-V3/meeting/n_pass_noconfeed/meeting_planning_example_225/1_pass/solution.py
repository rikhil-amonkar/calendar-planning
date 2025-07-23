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
        'duration': 60,
    },
    'Jeffrey': {
        'location': 'Union Square',
        'available_start': '15:00',
        'available_end': '22:00',
        'duration': 75,
    },
    'Brian': {
        'location': 'Alamo Square',
        'available_start': '16:00',
        'available_end': '17:30',
        'duration': 75,
    }
}

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

# Generate all possible orders to meet friends
friend_names = list(friends.keys())
best_itinerary = []
max_meetings = 0

for order in permutations(friend_names):
    itinerary = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for name in order:
        friend = friends[name]
        loc = friend['location']
        travel_time = travel_times[(temp_location, loc)]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        duration = friend['duration']
        
        # Calculate possible meeting window
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time <= available_end:
            if name == 'Brian' and end_time > time_to_minutes('17:30'):
                continue  # Brian's hard end time is 17:30
            itinerary.append({
                'action': 'meet',
                'location': loc,
                'person': name,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time),
            })
            meetings += 1
            temp_location = loc
            temp_time = end_time
    
    if meetings > max_meetings:
        max_meetings = meetings
        best_itinerary = itinerary
    elif meetings == max_meetings and meetings > 0:
        # Prefer the itinerary that ends earlier
        if not best_itinerary or temp_time < time_to_minutes(best_itinerary[-1]['end_time']):
            best_itinerary = itinerary

# Output the result
output = {
    "itinerary": best_itinerary
}
print(json.dumps(output, indent=2))
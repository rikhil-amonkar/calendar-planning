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
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4
}

friends = {
    'Anthony': {
        'location': 'Chinatown',
        'available_start': time_to_minutes('13:15'),
        'available_end': time_to_minutes('14:30'),
        'duration': 60
    },
    'Rebecca': {
        'location': 'Russian Hill',
        'available_start': time_to_minutes('19:30'),
        'available_end': time_to_minutes('21:15'),
        'duration': 105
    },
    'Melissa': {
        'location': 'North Beach',
        'available_start': time_to_minutes('8:15'),
        'available_end': time_to_minutes('13:30'),
        'duration': 105
    }
}

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

# Generate all possible orders to meet friends
friend_names = list(friends.keys())
possible_orders = permutations(friend_names)

best_schedule = None
best_meetings = 0

for order in possible_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for name in order:
        friend = friends[name]
        loc = friend['location']
        travel_time = travel_times[(temp_location, loc)]
        arrival_time = temp_time + travel_time
        
        # Check if we can meet the friend
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['duration']
        
        if end_time <= friend['available_end']:
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': name,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            meetings += 1
            temp_location = loc
            temp_time = end_time
        else:
            break
    
    if meetings > best_meetings or (meetings == best_meetings and best_schedule is None):
        best_meetings = meetings
        best_schedule = schedule

# If we can't meet all friends, try subsets
if best_meetings < 3:
    for subset_size in [2, 1]:
        for order in permutations(friend_names, subset_size):
            schedule = []
            temp_location = current_location
            temp_time = current_time
            meetings = 0
            
            for name in order:
                friend = friends[name]
                loc = friend['location']
                travel_time = travel_times[(temp_location, loc)]
                arrival_time = temp_time + travel_time
                
                start_time = max(arrival_time, friend['available_start'])
                end_time = start_time + friend['duration']
                
                if end_time <= friend['available_end']:
                    schedule.append({
                        'action': 'meet',
                        'location': loc,
                        'person': name,
                        'start_time': minutes_to_time(start_time),
                        'end_time': minutes_to_time(end_time)
                    })
                    meetings += 1
                    temp_location = loc
                    temp_time = end_time
                else:
                    break
            
            if meetings > best_meetings or (meetings == best_meetings and best_schedule is None):
                best_meetings = meetings
                best_schedule = schedule

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
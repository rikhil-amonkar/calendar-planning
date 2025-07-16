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
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14
}

friends = {
    'Timothy': {
        'location': 'Alamo Square',
        'available_start': '12:00',
        'available_end': '16:15',
        'min_duration': 105
    },
    'Mark': {
        'location': 'Presidio',
        'available_start': '18:45',
        'available_end': '21:00',
        'min_duration': 60
    },
    'Joseph': {
        'location': 'Russian Hill',
        'available_start': '16:45',
        'available_end': '21:30',
        'min_duration': 60
    }
}

current_location = 'Golden Gate Park'
current_time = time_to_minutes('9:00')

# Generate all possible permutations of meeting friends
friend_names = list(friends.keys())
best_itinerary = []
max_meetings = 0

for perm in permutations(friend_names):
    temp_location = current_location
    temp_time = current_time
    itinerary = []
    valid = True
    
    for friend in perm:
        friend_info = friends[friend]
        location = friend_info['location']
        travel_time = travel_times[(temp_location, location)]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend_info['available_start'])
        available_end = time_to_minutes(friend_info['available_end'])
        min_duration = friend_info['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            valid = False
            break
        
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        temp_location = location
        temp_time = end_time
    
    if valid and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

# Check if we can meet all three friends
if max_meetings == 3:
    result = {'itinerary': best_itinerary}
else:
    # Try meeting two friends
    max_meetings = 0
    best_itinerary = []
    for perm in permutations(friend_names, 2):
        temp_location = current_location
        temp_time = current_time
        itinerary = []
        valid = True
        
        for friend in perm:
            friend_info = friends[friend]
            location = friend_info['location']
            travel_time = travel_times[(temp_location, location)]
            arrival_time = temp_time + travel_time
            
            available_start = time_to_minutes(friend_info['available_start'])
            available_end = time_to_minutes(friend_info['available_end'])
            min_duration = friend_info['min_duration']
            
            start_time = max(arrival_time, available_start)
            end_time = start_time + min_duration
            
            if end_time > available_end:
                valid = False
                break
            
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': friend,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            
            temp_location = location
            temp_time = end_time
        
        if valid and len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_itinerary = itinerary

    result = {'itinerary': best_itinerary}

print(json.dumps(result, indent=2))
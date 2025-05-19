import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22
}

# Friend constraints
friends = {
    'Rebecca': {
        'location': 'Mission District',
        'available_start': (11, 30),
        'available_end': (20, 15),
        'min_duration': 120
    },
    'Karen': {
        'location': 'Bayview',
        'available_start': (12, 45),
        'available_end': (15, 0),
        'min_duration': 120
    },
    'Carol': {
        'location': 'Sunset District',
        'available_start': (10, 15),
        'available_end': (11, 45),
        'min_duration': 30
    }
}

def time_to_minutes(time_tuple):
    return time_tuple[0] * 60 + time_tuple[1]

def minutes_to_time(minutes):
    return (minutes // 60, minutes % 60)

def format_time(time_tuple):
    return f"{time_tuple[0]}:{time_tuple[1]:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def is_schedule_valid(schedule):
    current_location = 'Union Square'
    current_time = time_to_minutes((9, 0))
    
    for friend in schedule:
        friend_info = friends[friend]
        location = friend_info['location']
        travel_time = get_travel_time(current_location, location)
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend_info['available_start'])
        available_end = time_to_minutes(friend_info['available_end'])
        min_duration = friend_info['min_duration']
        
        if arrival_time > available_end:
            return False
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            return False
        
        current_time = end_time
        current_location = location
    
    return True

def calculate_total_meeting_time(schedule):
    total = 0
    for friend in schedule:
        total += friends[friend]['min_duration']
    return total

def generate_itinerary(schedule):
    itinerary = []
    current_location = 'Union Square'
    current_time = time_to_minutes((9, 0))
    
    for friend in schedule:
        friend_info = friends[friend]
        location = friend_info['location']
        travel_time = get_travel_time(current_location, location)
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend_info['available_start'])
        available_end = time_to_minutes(friend_info['available_end'])
        min_duration = friend_info['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": format_time(minutes_to_time(start_time)),
            "end_time": format_time(minutes_to_time(end_time))
        })
        
        current_time = end_time
        current_location = location
    
    return itinerary

def find_optimal_schedule():
    friend_names = list(friends.keys())
    best_schedule = None
    best_time = 0
    
    for perm in permutations(friend_names):
        if is_schedule_valid(perm):
            total_time = calculate_total_meeting_time(perm)
            if total_time > best_time:
                best_time = total_time
                best_schedule = perm
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
if optimal_schedule:
    itinerary = generate_itinerary(optimal_schedule)
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))
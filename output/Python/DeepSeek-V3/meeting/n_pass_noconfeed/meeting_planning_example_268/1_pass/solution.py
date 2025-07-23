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
    ('Russian Hill', 'Presidio'): 14,
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

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
best_meetings = 0

for order in meeting_orders:
    schedule = []
    valid = True
    loc = current_location
    time = current_time
    
    for person in order:
        friend = friends[person]
        loc_to = friend['location']
        travel_time = travel_times[(loc, loc_to)]
        arrival_time = time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            valid = False
            break
        
        schedule.append({
            'action': 'meet',
            'location': loc_to,
            'person': person,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        loc = loc_to
        time = end_time
    
    if valid and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)

if best_schedule is None:
    # Try to meet as many as possible even if not all
    for num_meetings in range(2, 0, -1):
        for order in permutations(friends.keys(), num_meetings):
            schedule = []
            valid = True
            loc = current_location
            time = current_time
            
            for person in order:
                friend = friends[person]
                loc_to = friend['location']
                travel_time = travel_times[(loc, loc_to)]
                arrival_time = time + travel_time
                
                available_start = time_to_minutes(friend['available_start'])
                available_end = time_to_minutes(friend['available_end'])
                min_duration = friend['min_duration']
                
                start_time = max(arrival_time, available_start)
                end_time = start_time + min_duration
                
                if end_time > available_end:
                    valid = False
                    break
                
                schedule.append({
                    'action': 'meet',
                    'location': loc_to,
                    'person': person,
                    'start_time': minutes_to_time(start_time),
                    'end_time': minutes_to_time(end_time)
                })
                
                loc = loc_to
                time = end_time
            
            if valid:
                best_schedule = schedule
                best_meetings = len(schedule)
                break
        if best_schedule is not None:
            break

output = {"itinerary": best_schedule} if best_schedule else {"itinerary": []}
print(json.dumps(output, indent=2))
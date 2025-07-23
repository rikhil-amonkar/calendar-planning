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
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21
}

friends = {
    'Emily': {
        'location': 'Presidio',
        'available_start': '16:15',
        'available_end': '21:00',
        'duration': 105
    },
    'Joseph': {
        'location': 'Richmond District',
        'available_start': '17:15',
        'available_end': '22:00',
        'duration': 120
    },
    'Melissa': {
        'location': 'Financial District',
        'available_start': '15:45',
        'available_end': '21:45',
        'duration': 75
    }
}

current_location = 'Fisherman\'s Wharf'
current_time = time_to_minutes('9:00')

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
max_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    possible = True
    meetings_scheduled = 0
    
    for person in order:
        friend = friends[person]
        location = friend['location']
        travel_time = travel_times[(temp_location, location)]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        duration = friend['duration']
        
        # Calculate meeting start and end times
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time > available_end:
            possible = False
            break
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        temp_location = location
        temp_time = end_time
        meetings_scheduled += 1
    
    if possible and meetings_scheduled > max_meetings:
        max_meetings = meetings_scheduled
        best_schedule = schedule
    elif possible and meetings_scheduled == max_meetings:
        # Prefer schedules that end earlier
        if best_schedule is None or temp_time < time_to_minutes(best_schedule[-1]['end_time']):
            best_schedule = schedule

# Output the best schedule
if best_schedule is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_schedule}

print(json.dumps(result, indent=2))
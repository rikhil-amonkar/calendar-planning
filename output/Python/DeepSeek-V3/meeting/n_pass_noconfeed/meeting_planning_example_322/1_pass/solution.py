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
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Presidio'): 17
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
    met_friends = set()
    
    for friend in order:
        if friend in met_friends:
            continue
        friend_data = friends[friend]
        dest = friend_data['location']
        travel_time = travel_times[(loc, dest)]
        arrival_time = time + travel_time
        available_start = time_to_minutes(friend_data['available_start'])
        available_end = time_to_minutes(friend_data['available_end'])
        min_duration = friend_data['min_duration']
        
        start_meeting = max(arrival_time, available_start)
        end_meeting = start_meeting + min_duration
        
        if end_meeting > available_end:
            continue
        
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend,
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        
        met_friends.add(friend)
        loc = dest
        time = end_meeting
    
    # Check if we can meet William in the evening
    william_data = friends['William']
    if 'William' not in met_friends:
        dest = william_data['location']
        travel_time = travel_times[(loc, dest)]
        arrival_time = time + travel_time
        available_start = time_to_minutes(william_data['available_start'])
        available_end = time_to_minutes(william_data['available_end'])
        min_duration = william_data['min_duration']
        
        start_meeting = max(arrival_time, available_start)
        end_meeting = start_meeting + min_duration
        
        if end_meeting <= available_end:
            schedule.append({
                'action': 'meet',
                'location': dest,
                'person': 'William',
                'start_time': minutes_to_time(start_meeting),
                'end_time': minutes_to_time(end_meeting)
            })
            met_friends.add('William')
    
    return schedule, len(met_friends)

best_schedule = []
max_meetings = 0

# Try all possible orders of meeting friends (excluding William initially)
for order in permutations(['Michelle', 'George', 'Robert']):
    schedule, num_meetings = calculate_schedule(order)
    if num_meetings > max_meetings:
        max_meetings = num_meetings
        best_schedule = schedule
    elif num_meetings == max_meetings and len(schedule) < len(best_schedule):
        best_schedule = schedule

# Now try orders that include William early
for order in permutations(['William', 'Michelle', 'George', 'Robert']):
    schedule, num_meetings = calculate_schedule(order)
    if num_meetings > max_meetings:
        max_meetings = num_meetings
        best_schedule = schedule
    elif num_meetings == max_meetings and len(schedule) < len(best_schedule):
        best_schedule = schedule

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
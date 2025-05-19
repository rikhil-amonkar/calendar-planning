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

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
best_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for person in order:
        friend = friends[person]
        location = friend['location']
        travel_time = travel_times[(temp_location, location)]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Calculate possible meeting start and end times
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > available_end:
            continue  # Can't meet this friend
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        meetings += 1
        temp_location = location
        temp_time = meeting_end
    
    if meetings > best_meetings:
        best_meetings = meetings
        best_schedule = schedule
    elif meetings == best_meetings and best_schedule is None:
        best_schedule = schedule

if best_schedule is None:
    best_schedule = []

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
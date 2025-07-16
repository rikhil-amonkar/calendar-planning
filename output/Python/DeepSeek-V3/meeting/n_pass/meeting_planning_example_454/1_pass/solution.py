import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from_location, to_location): time
travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17
}

# Constraints
constraints = {
    'Jessica': {
        'location': 'Golden Gate Park',
        'start': time_to_minutes('13:45'),
        'end': time_to_minutes('15:00'),
        'min_duration': 30
    },
    'Ashley': {
        'location': 'Bayview',
        'start': time_to_minutes('17:15'),
        'end': time_to_minutes('20:00'),
        'min_duration': 105
    },
    'Ronald': {
        'location': 'Chinatown',
        'start': time_to_minutes('7:15'),
        'end': time_to_minutes('14:45'),
        'min_duration': 90
    },
    'William': {
        'location': 'North Beach',
        'start': time_to_minutes('13:15'),
        'end': time_to_minutes('20:15'),
        'min_duration': 15
    },
    'Daniel': {
        'location': 'Mission District',
        'start': time_to_minutes('7:00'),
        'end': time_to_minutes('11:15'),
        'min_duration': 105
    }
}

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    
    for meeting in schedule:
        person = meeting['person']
        constraint = constraints[person]
        location = constraint['location']
        
        # Travel to the meeting location
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Check if we can meet within the person's available time
        meeting_start = max(arrival_time, constraint['start'])
        meeting_end = meeting_start + constraint['min_duration']
        
        if meeting_end > constraint['end']:
            return False
        
        current_time = meeting_end
        current_location = location
    
    return True

def generate_schedules():
    people = list(constraints.keys())
    # Generate all possible orders of meeting people
    for order in permutations(people):
        schedule = []
        for person in order:
            schedule.append({
                'person': person,
                'location': constraints[person]['location']
            })
        if is_schedule_valid(schedule):
            yield schedule
    return None

def build_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    
    for meeting in schedule:
        person = meeting['person']
        constraint = constraints[person]
        location = constraint['location']
        
        # Travel to the meeting location
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Calculate meeting times
        meeting_start = max(arrival_time, constraint['start'])
        meeting_end = meeting_start + constraint['min_duration']
        
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return itinerary

# Find a valid schedule
valid_schedule = None
for schedule in generate_schedules():
    valid_schedule = schedule
    break

if valid_schedule:
    itinerary = build_itinerary(valid_schedule)
    result = {
        'itinerary': itinerary
    }
else:
    result = {
        'itinerary': []
    }

print(json.dumps(result, indent=2))
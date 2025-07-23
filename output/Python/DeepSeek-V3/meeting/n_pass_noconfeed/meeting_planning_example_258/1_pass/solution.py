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
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18
}

friends = {
    'Betty': {
        'location': 'Presidio',
        'available_start': '10:15',
        'available_end': '21:30',
        'duration': 45
    },
    'David': {
        'location': 'Richmond District',
        'available_start': '13:00',
        'available_end': '20:15',
        'duration': 90
    },
    'Barbara': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:15',
        'available_end': '20:15',
        'duration': 120
    }
}

current_location = 'Embarcadero'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for person in order:
        friend = friends[person]
        dest = friend['location']
        
        # Travel time
        travel_key = (loc, dest)
        travel_time = travel_times.get(travel_key, 0)
        arrival_time = time + travel_time
        
        # Available window
        avail_start = time_to_minutes(friend['available_start'])
        avail_end = time_to_minutes(friend['available_end'])
        duration = friend['duration']
        
        # Calculate meeting window
        start_time = max(arrival_time, avail_start)
        end_time = start_time + duration
        
        if end_time > avail_end:
            return None  # Doesn't fit
        
        schedule.append({
            'person': person,
            'location': dest,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time),
            'departure_time': end_time
        })
        
        loc = dest
        time = end_time
    
    return schedule

# Try all possible meeting orders
best_schedule = None
max_meetings = 0

for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > max_meetings:
        best_schedule = schedule
        max_meetings = len(schedule)

# Prepare output
if best_schedule:
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": meeting['start_time'],
            "end_time": meeting['end_time']
        })
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output, indent=2))
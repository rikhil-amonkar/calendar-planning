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
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

friends = {
    'Betty': {
        'location': 'Presidio',
        'available_start': '10:15',
        'available_end': '21:30',
        'min_duration': 45
    },
    'David': {
        'location': 'Richmond District',
        'available_start': '13:00',
        'available_end': '20:15',
        'min_duration': 90
    },
    'Barbara': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:15',
        'available_end': '20:15',
        'min_duration': 120
    }
}

current_location = 'Embarcadero'
current_time = time_to_minutes('9:00')

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
best_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = []
    
    for person in order:
        friend = friends[person]
        loc = friend['location']
        travel_time = travel_times[(temp_location, loc)]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            continue  # Can't meet this friend in this order
        
        meetings.append({
            'person': person,
            'location': loc,
            'start_time': start_time,
            'end_time': end_time
        })
        
        temp_location = loc
        temp_time = end_time
    
    if len(meetings) > best_meetings or (len(meetings) == best_meetings and best_schedule is None):
        best_meetings = len(meetings)
        best_schedule = meetings

# Convert to itinerary format
itinerary = []
if best_schedule:
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": minutes_to_time(meeting['start_time']),
            "end_time": minutes_to_time(meeting['end_time'])
        })

# Output as JSON
output = {
    "itinerary": itinerary
}
print(json.dumps(output, indent=2))
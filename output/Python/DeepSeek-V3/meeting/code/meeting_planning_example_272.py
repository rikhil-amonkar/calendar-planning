import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20
}

friends = {
    'Patricia': {
        'location': 'Nob Hill',
        'available_start': '18:30',
        'available_end': '21:45',
        'min_duration': 90
    },
    'Ashley': {
        'location': 'Mission District',
        'available_start': '20:30',
        'available_end': '21:15',
        'min_duration': 45
    },
    'Timothy': {
        'location': 'Embarcadero',
        'available_start': '9:45',
        'available_end': '17:45',
        'min_duration': 120
    }
}

current_location = 'Russian Hill'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    current_loc = current_location
    current_time_val = current_time
    
    for friend in order:
        friend_data = friends[friend]
        loc = friend_data['location']
        travel_time = travel_times[(current_loc, loc)]
        
        arrival_time = current_time_val + travel_time
        available_start = time_to_minutes(friend_data['available_start'])
        available_end = time_to_minutes(friend_data['available_end'])
        min_duration = friend_data['min_duration']
        
        # Calculate meeting start and end
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            return None  # Doesn't meet duration requirement
        
        schedule.append({
            'friend': friend,
            'location': loc,
            'start_time': start_time,
            'end_time': end_time,
            'travel_time': travel_time
        })
        
        current_loc = loc
        current_time_val = end_time
    
    return schedule

# Generate all possible meeting orders
friend_names = list(friends.keys())
possible_orders = permutations(friend_names)

best_schedule = None
best_meetings = 0

for order in possible_orders:
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)
    elif schedule and len(schedule) == best_meetings:
        # Prefer schedules that meet more people earlier
        pass

if not best_schedule:
    # Try to meet as many as possible even if not all
    for num_to_meet in range(len(friend_names)-1, 0, -1):
        for order in permutations(friend_names, num_to_meet):
            schedule = calculate_schedule(order)
            if schedule:
                best_schedule = schedule
                best_meetings = len(schedule)
                break
        if best_schedule:
            break

# Prepare output
output = {"itinerary": []}
if best_schedule:
    for meeting in best_schedule:
        output["itinerary"].append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": minutes_to_time(meeting['start_time']),
            "end_time": minutes_to_time(meeting['end_time'])
        })

print(json.dumps(output, indent=2))
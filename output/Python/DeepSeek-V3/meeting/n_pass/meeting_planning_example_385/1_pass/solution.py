import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str is None:
        return 0
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Pacific Heights'): 11,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
}

friends = {
    'Jeffrey': {
        'location': 'Presidio',
        'available_start': '8:00',
        'available_end': '10:00',
        'min_duration': 105
    },
    'Steven': {
        'location': 'North Beach',
        'available_start': '13:30',
        'available_end': '22:00',
        'min_duration': 45
    },
    'Barbara': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '18:00',
        'available_end': '21:30',
        'min_duration': 30
    },
    'John': {
        'location': 'Pacific Heights',
        'available_start': '9:00',
        'available_end': '13:30',
        'min_duration': 15
    }
}

current_location = 'Nob Hill'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    for friend in order:
        details = friends[friend]
        travel_time = travel_times.get((loc, details['location']), 0)
        arrival_time = time + travel_time
        available_start = time_to_minutes(details['available_start'])
        available_end = time_to_minutes(details['available_end'])
        
        # Check if arrival is before available_end
        if arrival_time >= available_end:
            return None
        
        # Start time is max of arrival and available_start
        start_time = max(arrival_time, available_start)
        end_time = start_time + details['min_duration']
        
        if end_time > available_end:
            return None
        
        schedule.append({
            'friend': friend,
            'location': details['location'],
            'start_time': start_time,
            'end_time': end_time,
            'travel_time': travel_time
        })
        
        loc = details['location']
        time = end_time
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    # Count number of friends met
    return len(schedule)

best_schedule = None
best_score = 0

# Try all possible orders of friends
for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

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
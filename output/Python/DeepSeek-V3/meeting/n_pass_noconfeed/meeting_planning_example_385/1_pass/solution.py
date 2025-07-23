import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

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
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13
}

friends = [
    {
        'name': 'Jeffrey',
        'location': 'Presidio',
        'available_start': '8:00',
        'available_end': '10:00',
        'min_duration': 105
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': '13:30',
        'available_end': '22:00',
        'min_duration': 45
    },
    {
        'name': 'Barbara',
        'location': 'Fisherman\'s Wharf',
        'available_start': '18:00',
        'available_end': '21:30',
        'min_duration': 30
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': '9:00',
        'available_end': '13:30',
        'min_duration': 15
    }
]

current_location = 'Nob Hill'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for friend_idx in order:
        friend = friends[friend_idx]
        dest = friend['location']
        
        # Travel time
        travel_time = travel_times[(loc, dest)]
        arrival_time = time + travel_time
        
        # Check if we can meet
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Adjust arrival time if we arrive too early
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            return None  # Can't meet this friend
        
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        # Update current time and location
        time = end_time
        loc = dest
    
    return schedule

# Try all possible orders to find the best schedule
best_schedule = None
best_meetings = 0

for order in permutations(range(4)):
    schedule = calculate_schedule(order)
    if schedule is not None and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)

if best_schedule is None:
    # Try to find partial schedules if full schedule isn't possible
    for num_meetings in range(3, 0, -1):
        for order in permutations(range(4), num_meetings):
            schedule = calculate_schedule(order)
            if schedule is not None and len(schedule) > best_meetings:
                best_schedule = schedule
                best_meetings = len(schedule)
            if best_schedule is not None:
                break
        if best_schedule is not None:
            break

output = {
    "itinerary": best_schedule if best_schedule is not None else []
}

print(json.dumps(output, indent=2))
import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'North Beach': {
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Mission District': 18,
        'Golden Gate Park': 22,
        'Nob Hill': 7
    },
    'Pacific Heights': {
        'North Beach': 9,
        'Chinatown': 11,
        'Union Square': 12,
        'Mission District': 15,
        'Golden Gate Park': 15,
        'Nob Hill': 8
    },
    'Chinatown': {
        'North Beach': 3,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Mission District': 18,
        'Golden Gate Park': 23,
        'Nob Hill': 8
    },
    'Union Square': {
        'North Beach': 10,
        'Pacific Heights': 15,
        'Chinatown': 7,
        'Mission District': 14,
        'Golden Gate Park': 22,
        'Nob Hill': 9
    },
    'Mission District': {
        'North Beach': 17,
        'Pacific Heights': 16,
        'Chinatown': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Nob Hill': 12
    },
    'Golden Gate Park': {
        'North Beach': 24,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Union Square': 22,
        'Mission District': 17,
        'Nob Hill': 20
    },
    'Nob Hill': {
        'North Beach': 8,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Mission District': 13,
        'Golden Gate Park': 17
    }
}

friends = {
    'James': {
        'location': 'Pacific Heights',
        'available_start': '20:00',
        'available_end': '22:00',
        'min_duration': 120
    },
    'Robert': {
        'location': 'Chinatown',
        'available_start': '12:15',
        'available_end': '16:45',
        'min_duration': 90
    },
    'Jeffrey': {
        'location': 'Union Square',
        'available_start': '9:30',
        'available_end': '15:30',
        'min_duration': 120
    },
    'Carol': {
        'location': 'Mission District',
        'available_start': '18:15',
        'available_end': '21:15',
        'min_duration': 15
    },
    'Mark': {
        'location': 'Golden Gate Park',
        'available_start': '11:30',
        'available_end': '17:45',
        'min_duration': 15
    },
    'Sandra': {
        'location': 'Nob Hill',
        'available_start': '8:00',
        'available_end': '15:30',
        'min_duration': 15
    }
}

current_location = 'North Beach'
current_time = time_to_minutes('9:00')
itinerary = []

def calculate_schedule(order):
    global current_location, current_time, itinerary
    current_location = 'North Beach'
    current_time = time_to_minutes('9:00')
    itinerary = []
    
    for friend in order:
        friend_data = friends[friend]
        location = friend_data['location']
        available_start = time_to_minutes(friend_data['available_start'])
        available_end = time_to_minutes(friend_data['available_end'])
        min_duration = friend_data['min_duration']
        
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        if arrival_time > available_end:
            return None
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            return None
        
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = location
    
    return itinerary

best_schedule = None
best_count = 0

# Try all possible orders of friends
for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_count:
        best_schedule = schedule
        best_count = len(schedule)

# If no schedule meets all friends, try subsets
if best_count < len(friends):
    for friend_count in range(len(friends), 0, -1):
        for order in permutations(friends.keys(), friend_count):
            schedule = calculate_schedule(order)
            if schedule and len(schedule) > best_count:
                best_schedule = schedule
                best_count = len(schedule)
                if best_count == friend_count:
                    break
        if best_count == friend_count:
            break

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
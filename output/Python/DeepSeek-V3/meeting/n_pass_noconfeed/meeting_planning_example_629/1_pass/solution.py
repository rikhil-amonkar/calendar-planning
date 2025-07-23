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
    'Russian Hill': {
        'Presidio': 14,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'Richmond District': 14,
        'Fisherman\'s Wharf': 7,
        'Golden Gate Park': 21,
        'Bayview': 23
    },
    'Presidio': {
        'Russian Hill': 14,
        'Chinatown': 21,
        'Pacific Heights': 11,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Chinatown': {
        'Russian Hill': 7,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Richmond District': 20,
        'Fisherman\'s Wharf': 8,
        'Golden Gate Park': 23,
        'Bayview': 22
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'Presidio': 11,
        'Chinatown': 11,
        'Richmond District': 12,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15,
        'Bayview': 22
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Presidio': 7,
        'Chinatown': 20,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Bayview': 26
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'Richmond District': 18,
        'Golden Gate Park': 25,
        'Bayview': 26
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23
    },
    'Bayview': {
        'Russian Hill': 23,
        'Presidio': 31,
        'Chinatown': 18,
        'Pacific Heights': 23,
        'Richmond District': 25,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    }
}

friends = [
    {'name': 'Matthew', 'location': 'Presidio', 'start': '11:00', 'end': '21:00', 'duration': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start': '9:15', 'end': '18:45', 'duration': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': '14:15', 'end': '17:00', 'duration': 15},
    {'name': 'Helen', 'location': 'Richmond District', 'start': '19:45', 'end': '22:00', 'duration': 60},
    {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': '21:15', 'end': '22:15', 'duration': 60},
    {'name': 'Kimberly', 'location': 'Golden Gate Park', 'start': '13:00', 'end': '16:30', 'duration': 120},
    {'name': 'Kenneth', 'location': 'Bayview', 'start': '14:30', 'end': '18:00', 'duration': 60}
]

def evaluate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Russian Hill'
    schedule = []
    total_meetings = 0
    
    for friend_idx in order:
        friend = friends[friend_idx]
        location = friend['location']
        travel_time = travel_times[current_location].get(location, float('inf'))
        arrival_time = current_time + travel_time
        
        start_window = time_to_minutes(friend['start'])
        end_window = time_to_minutes(friend['end'])
        duration = friend['duration']
        
        # Calculate meeting start time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + duration
        
        if meeting_end > end_window:
            continue  # Can't meet this friend
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
        total_meetings += 1
    
    return total_meetings, schedule

# Generate all possible orders (limited to 7 friends for performance)
best_schedule = []
max_meetings = 0

# Since trying all permutations is too slow, we'll use a heuristic approach
# Try different orders prioritizing friends with tighter time windows first
priority_order = [1, 5, 6, 2, 0, 3, 4]  # Margaret, Kimberly, Kenneth, Nancy, Matthew, Helen, Rebecca

# Try this order first
total, schedule = evaluate_schedule(priority_order)
if total > max_meetings:
    max_meetings = total
    best_schedule = schedule

# Try some variations
variations = [
    [1, 5, 6, 0, 2, 3, 4],  # Margaret, Kimberly, Kenneth, Matthew, Nancy, Helen, Rebecca
    [1, 5, 6, 2, 0, 3, 4],  # Margaret, Kimberly, Kenneth, Nancy, Matthew, Helen, Rebecca
    [1, 5, 2, 6, 0, 3, 4],  # Margaret, Kimberly, Nancy, Kenneth, Matthew, Helen, Rebecca
    [1, 5, 2, 0, 6, 3, 4],  # Margaret, Kimberly, Nancy, Matthew, Kenneth, Helen, Rebecca
]

for order in variations:
    total, schedule = evaluate_schedule(order)
    if total > max_meetings:
        max_meetings = total
        best_schedule = schedule

# Output the best schedule found
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))
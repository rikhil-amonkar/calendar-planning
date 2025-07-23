import json
from itertools import permutations

# Travel times in minutes between locations
travel_times = {
    'Union Square': {
        'Golden Gate Park': 22,
        'Pacific Heights': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'The Castro': 19
    },
    'Golden Gate Park': {
        'Union Square': 22,
        'Pacific Heights': 16,
        'Presidio': 11,
        'Chinatown': 23,
        'The Castro': 13
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Presidio': 11,
        'Chinatown': 11,
        'The Castro': 16
    },
    'Presidio': {
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Pacific Heights': 11,
        'Chinatown': 21,
        'The Castro': 21
    },
    'Chinatown': {
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Pacific Heights': 10,
        'Presidio': 19,
        'The Castro': 22
    },
    'The Castro': {
        'Union Square': 19,
        'Golden Gate Park': 11,
        'Pacific Heights': 16,
        'Presidio': 20,
        'Chinatown': 20
    }
}

# Friend availability and constraints
friends = {
    'Andrew': {
        'location': 'Golden Gate Park',
        'start': '11:45',
        'end': '14:30',
        'min_duration': 75
    },
    'Sarah': {
        'location': 'Pacific Heights',
        'start': '16:15',
        'end': '18:45',
        'min_duration': 15
    },
    'Nancy': {
        'location': 'Presidio',
        'start': '17:30',
        'end': '19:15',
        'min_duration': 60
    },
    'Rebecca': {
        'location': 'Chinatown',
        'start': '9:45',
        'end': '21:30',
        'min_duration': 90
    },
    'Robert': {
        'location': 'The Castro',
        'start': '8:30',
        'end': '14:15',
        'min_duration': 30
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_meet(friend, start_time, end_time):
    friend_start = time_to_minutes(friend['start'])
    friend_end = time_to_minutes(friend['end'])
    return start_time >= friend_start and end_time <= friend_end and (end_time - start_time) >= friend['min_duration']

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    schedule = []
    
    for friend_name in order:
        friend = friends[friend_name]
        destination = friend['location']
        
        # Travel time
        travel_time = travel_times[current_location][destination]
        arrival_time = current_time + travel_time
        
        # Meeting time
        min_duration = friend['min_duration']
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, friend_start)
        meeting_end = min(meeting_start + min_duration, friend_end)
        
        if meeting_end - meeting_start < min_duration:
            return None  # Can't meet this friend with current order
        
        # Add to schedule
        schedule.append({
            'action': 'meet',
            'location': destination,
            'person': friend_name,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = destination
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    # Count number of friends met
    return len(schedule)

# Generate all possible orders of meeting friends
all_orders = permutations(friends.keys())
best_schedule = None
best_score = 0

for order in all_orders:
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# Output the best schedule
if best_schedule:
    output = {'itinerary': best_schedule}
else:
    output = {'itinerary': []}

print(json.dumps(output, indent=2))
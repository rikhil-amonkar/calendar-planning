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
    'Financial District': {
        'Russian Hill': 10,
        'Sunset District': 31,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23
    },
    'Russian Hill': {
        'Financial District': 11,
        'Sunset District': 23,
        'North Beach': 5,
        'The Castro': 21,
        'Golden Gate Park': 21
    },
    'Sunset District': {
        'Financial District': 30,
        'Russian Hill': 24,
        'North Beach': 29,
        'The Castro': 17,
        'Golden Gate Park': 11
    },
    'North Beach': {
        'Financial District': 8,
        'Russian Hill': 4,
        'Sunset District': 27,
        'The Castro': 22,
        'Golden Gate Park': 22
    },
    'The Castro': {
        'Financial District': 20,
        'Russian Hill': 18,
        'Sunset District': 17,
        'North Beach': 20,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Russian Hill': 19,
        'Sunset District': 10,
        'North Beach': 24,
        'The Castro': 13
    }
}

friends = {
    'Ronald': {
        'location': 'Russian Hill',
        'available_start': time_to_minutes('13:45'),
        'available_end': time_to_minutes('17:15'),
        'min_duration': 105
    },
    'Patricia': {
        'location': 'Sunset District',
        'available_start': time_to_minutes('9:15'),
        'available_end': time_to_minutes('22:00'),
        'min_duration': 60
    },
    'Laura': {
        'location': 'North Beach',
        'available_start': time_to_minutes('12:30'),
        'available_end': time_to_minutes('12:45'),
        'min_duration': 15
    },
    'Emily': {
        'location': 'The Castro',
        'available_start': time_to_minutes('16:15'),
        'available_end': time_to_minutes('18:30'),
        'min_duration': 60
    },
    'Mary': {
        'location': 'Golden Gate Park',
        'available_start': time_to_minutes('15:00'),
        'available_end': time_to_minutes('16:30'),
        'min_duration': 60
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['min_duration']
        
        if end_time > friend['available_end']:
            return None  # Can't meet this friend
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend_name,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        met_friends.add(friend_name)
        current_time = end_time
        current_location = location
    
    return {
        'itinerary': schedule,
        'met_count': len(met_friends)
    }

# Generate all possible orders of meeting friends
all_orders = permutations(friends.keys())
best_schedule = None
best_met = 0

for order in all_orders:
    schedule = calculate_schedule(order)
    if schedule and schedule['met_count'] > best_met:
        best_schedule = schedule
        best_met = schedule['met_count']

if best_schedule:
    print(json.dumps({'itinerary': best_schedule['itinerary']}, indent=2))
else:
    print(json.dumps({'itinerary': []}, indent=2))
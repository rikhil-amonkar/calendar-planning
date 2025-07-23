import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'Embarcadero': {
        'Bayview': 21, 'Chinatown': 7, 'Alamo Square': 19, 'Nob Hill': 10, 'Presidio': 20,
        'Union Square': 10, 'The Castro': 25, 'North Beach': 5, 'Fisherman\'s Wharf': 6, 'Marina District': 12
    },
    'Bayview': {
        'Embarcadero': 19, 'Chinatown': 19, 'Alamo Square': 16, 'Nob Hill': 20, 'Presidio': 32,
        'Union Square': 18, 'The Castro': 19, 'North Beach': 22, 'Fisherman\'s Wharf': 25, 'Marina District': 27
    },
    'Chinatown': {
        'Embarcadero': 5, 'Bayview': 20, 'Alamo Square': 17, 'Nob Hill': 9, 'Presidio': 19,
        'Union Square': 7, 'The Castro': 22, 'North Beach': 3, 'Fisherman\'s Wharf': 8, 'Marina District': 12
    },
    'Alamo Square': {
        'Embarcadero': 16, 'Bayview': 16, 'Chinatown': 15, 'Nob Hill': 11, 'Presidio': 17,
        'Union Square': 14, 'The Castro': 8, 'North Beach': 15, 'Fisherman\'s Wharf': 19, 'Marina District': 15
    },
    'Nob Hill': {
        'Embarcadero': 9, 'Bayview': 19, 'Chinatown': 6, 'Alamo Square': 11, 'Presidio': 17,
        'Union Square': 7, 'The Castro': 17, 'North Beach': 8, 'Fisherman\'s Wharf': 10, 'Marina District': 11
    },
    'Presidio': {
        'Embarcadero': 20, 'Bayview': 31, 'Chinatown': 21, 'Alamo Square': 19, 'Nob Hill': 18,
        'Union Square': 22, 'The Castro': 21, 'North Beach': 18, 'Fisherman\'s Wharf': 19, 'Marina District': 11
    },
    'Union Square': {
        'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7, 'Alamo Square': 15, 'Nob Hill': 9,
        'Presidio': 24, 'The Castro': 17, 'North Beach': 10, 'Fisherman\'s Wharf': 15, 'Marina District': 18
    },
    'The Castro': {
        'Embarcadero': 22, 'Bayview': 19, 'Chinatown': 22, 'Alamo Square': 8, 'Nob Hill': 16,
        'Presidio': 20, 'Union Square': 19, 'North Beach': 20, 'Fisherman\'s Wharf': 24, 'Marina District': 21
    },
    'North Beach': {
        'Embarcadero': 6, 'Bayview': 25, 'Chinatown': 6, 'Alamo Square': 16, 'Nob Hill': 7,
        'Presidio': 17, 'Union Square': 7, 'The Castro': 23, 'Fisherman\'s Wharf': 5, 'Marina District': 9
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8, 'Bayview': 26, 'Chinatown': 12, 'Alamo Square': 21, 'Nob Hill': 11,
        'Presidio': 17, 'Union Square': 13, 'The Castro': 27, 'North Beach': 6, 'Marina District': 9
    },
    'Marina District': {
        'Embarcadero': 14, 'Bayview': 27, 'Chinatown': 15, 'Alamo Square': 15, 'Nob Hill': 12,
        'Presidio': 10, 'Union Square': 16, 'The Castro': 22, 'North Beach': 11, 'Fisherman\'s Wharf': 10
    }
}

# Friend constraints
friends = {
    'Matthew': {'location': 'Bayview', 'start': '19:15', 'end': '22:00', 'min_duration': 120},
    'Karen': {'location': 'Chinatown', 'start': '19:15', 'end': '21:15', 'min_duration': 90},
    'Sarah': {'location': 'Alamo Square', 'start': '20:00', 'end': '21:45', 'min_duration': 105},
    'Jessica': {'location': 'Nob Hill', 'start': '16:30', 'end': '18:45', 'min_duration': 120},
    'Stephanie': {'location': 'Presidio', 'start': '7:30', 'end': '10:15', 'min_duration': 60},
    'Mary': {'location': 'Union Square', 'start': '16:45', 'end': '21:30', 'min_duration': 60},
    'Charles': {'location': 'The Castro', 'start': '16:30', 'end': '22:00', 'min_duration': 105},
    'Nancy': {'location': 'North Beach', 'start': '14:45', 'end': '20:00', 'min_duration': 15},
    'Thomas': {'location': 'Fisherman\'s Wharf', 'start': '13:30', 'end': '19:00', 'min_duration': 30},
    'Brian': {'location': 'Marina District', 'start': '12:15', 'end': '18:00', 'min_duration': 60}
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_meet(current_time, friend, current_location):
    loc = friend['location']
    travel_time = travel_times[current_location][loc]
    arrival_time = current_time + travel_time
    start = time_to_minutes(friend['start'])
    end = time_to_minutes(friend['end'])
    min_duration = friend['min_duration']
    
    if arrival_time > end:
        return None
    
    meet_start = max(arrival_time, start)
    meet_end = min(meet_start + min_duration, end)
    
    if meet_end - meet_start >= min_duration:
        return (meet_start, meet_end)
    else:
        return None

def evaluate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Embarcadero'
    schedule = []
    met_friends = set()
    
    # First, meet Stephanie if possible
    stephanie = friends['Stephanie']
    if can_meet(current_time, stephanie, current_location):
        meet_start, meet_end = can_meet(current_time, stephanie, current_location)
        schedule.append({
            'action': 'meet',
            'location': stephanie['location'],
            'person': 'Stephanie',
            'start_time': minutes_to_time(meet_start),
            'end_time': minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = stephanie['location']
        met_friends.add('Stephanie')
    
    for friend_name in order:
        if friend_name in met_friends:
            continue
        friend = friends[friend_name]
        meeting = can_meet(current_time, friend, current_location)
        if meeting:
            meet_start, meet_end = meeting
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend_name,
                'start_time': minutes_to_time(meet_start),
                'end_time': minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = friend['location']
            met_friends.add(friend_name)
    
    return schedule, len(met_friends)

# Generate possible orders to meet friends (excluding Stephanie)
friend_names = [name for name in friends.keys() if name != 'Stephanie']
best_schedule = []
max_met = 0

# Try permutations to find best schedule
for perm in permutations(friend_names, min(5, len(friend_names))):  # Limit permutations for performance
    schedule, met = evaluate_schedule(perm)
    if met > max_met:
        max_met = met
        best_schedule = schedule

# Output the best schedule found
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
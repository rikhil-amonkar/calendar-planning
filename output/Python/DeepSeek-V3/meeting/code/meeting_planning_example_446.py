import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Richmond District': {
        'Marina District': 9,
        'Chinatown': 20,
        'Financial District': 22,
        'Bayview': 26,
        'Union Square': 21
    },
    'Marina District': {
        'Richmond District': 11,
        'Chinatown': 16,
        'Financial District': 17,
        'Bayview': 27,
        'Union Square': 16
    },
    'Chinatown': {
        'Richmond District': 20,
        'Marina District': 12,
        'Financial District': 5,
        'Bayview': 22,
        'Union Square': 7
    },
    'Financial District': {
        'Richmond District': 21,
        'Marina District': 15,
        'Chinatown': 5,
        'Bayview': 19,
        'Union Square': 9
    },
    'Bayview': {
        'Richmond District': 25,
        'Marina District': 25,
        'Chinatown': 18,
        'Financial District': 19,
        'Union Square': 17
    },
    'Union Square': {
        'Richmond District': 20,
        'Marina District': 18,
        'Chinatown': 7,
        'Financial District': 9,
        'Bayview': 15
    }
}

# Friend constraints
friends = [
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'start': '13:15',
        'end': '16:45',
        'duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start': '12:15',
        'end': '20:15',
        'duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'start': '13:15',
        'end': '16:45',
        'duration': 75
    },
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'start': '9:30',
        'end': '13:30',
        'duration': 30
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'start': '19:30',
        'end': '21:15',
        'duration': 75
    }
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_meet(current_time, friend, current_location):
    start = time_to_minutes(friend['start'])
    end = time_to_minutes(friend['end'])
    travel_time = travel_times[current_location][friend['location']]
    
    arrival_time = current_time + travel_time
    if arrival_time > end:
        return None
    
    meeting_start = max(arrival_time, start)
    meeting_end = meeting_start + friend['duration']
    
    if meeting_end > end:
        return None
    
    return {
        'start': meeting_start,
        'end': meeting_end,
        'location': friend['location'],
        'name': friend['name'],
        'travel_time': travel_time
    }

def evaluate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Richmond District'
    itinerary = []
    met_friends = set()
    
    # First try to meet Margaret in the morning
    margaret = next(f for f in friends if f['name'] == 'Margaret')
    meeting = can_meet(current_time, margaret, current_location)
    if meeting:
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['name'],
            'start_time': minutes_to_time(meeting['start']),
            'end_time': minutes_to_time(meeting['end'])
        })
        current_time = meeting['end']
        current_location = meeting['location']
        met_friends.add('Margaret')
    
    # Then try to meet others in the given order
    for friend_name in order:
        if friend_name in met_friends:
            continue
            
        friend = next(f for f in friends if f['name'] == friend_name)
        meeting = can_meet(current_time, friend, current_location)
        if meeting:
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['name'],
                'start_time': minutes_to_time(meeting['start']),
                'end_time': minutes_to_time(meeting['end'])
            })
            current_time = meeting['end']
            current_location = meeting['location']
            met_friends.add(friend_name)
    
    # Finally try to meet Kenneth in the evening
    kenneth = next(f for f in friends if f['name'] == 'Kenneth')
    if 'Kenneth' not in met_friends:
        meeting = can_meet(current_time, kenneth, current_location)
        if meeting:
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['name'],
                'start_time': minutes_to_time(meeting['start']),
                'end_time': minutes_to_time(meeting['end'])
            })
            met_friends.add('Kenneth')
    
    return {
        'itinerary': itinerary,
        'met_count': len(met_friends)
    }

# Generate all possible orders of meeting friends (excluding Margaret and Kenneth)
friend_names = [f['name'] for f in friends if f['name'] not in ['Margaret', 'Kenneth']]
best_schedule = None
best_count = 0

# Try all permutations of the remaining friends
for order in permutations(friend_names):
    schedule = evaluate_schedule(order)
    if schedule['met_count'] > best_count:
        best_count = schedule['met_count']
        best_schedule = schedule
    elif schedule['met_count'] == best_count and len(schedule['itinerary']) > len(best_schedule['itinerary']):
        best_schedule = schedule

print(json.dumps(best_schedule, indent=2))
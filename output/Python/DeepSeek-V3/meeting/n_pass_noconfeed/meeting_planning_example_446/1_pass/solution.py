import json
from itertools import permutations

# Travel times dictionary
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
    friend_start = time_to_minutes(friend['start'])
    friend_end = time_to_minutes(friend['end'])
    travel_time = travel_times[current_location][friend['location']]
    
    arrival_time = current_time + travel_time
    if arrival_time > friend_end:
        return None
    
    start_time = max(arrival_time, friend_start)
    end_time = start_time + friend['duration']
    
    if end_time > friend_end:
        return None
    
    return {
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    }, end_time

def evaluate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Richmond District'
    itinerary = []
    
    for friend_idx in order:
        friend = friends[friend_idx]
        meeting = can_meet(current_time, friend, current_location)
        if not meeting:
            return None
        itinerary.append(meeting[0])
        current_time = meeting[1]
        current_location = friend['location']
    
    return itinerary

def find_best_schedule():
    best_itinerary = None
    max_meetings = 0
    
    # Try all possible permutations of meeting orders
    for order in permutations(range(len(friends))):
        itinerary = evaluate_schedule(order)
        if itinerary and len(itinerary) > max_meetings:
            best_itinerary = itinerary
            max_meetings = len(itinerary)
        elif itinerary and len(itinerary) == max_meetings:
            # Prefer longer meetings if same number of friends met
            total_duration = sum(time_to_minutes(m['end_time']) - time_to_minutes(m['start_time']) for m in itinerary)
            current_duration = sum(time_to_minutes(m['end_time']) - time_to_minutes(m['start_time']) for m in best_itinerary) if best_itinerary else 0
            if total_duration > current_duration:
                best_itinerary = itinerary
    
    return best_itinerary

best_schedule = find_best_schedule()
if best_schedule:
    result = {'itinerary': best_schedule}
else:
    result = {'itinerary': []}

print(json.dumps(result, indent=2))
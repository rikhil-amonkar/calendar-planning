import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'Russian Hill': {
        'Marina District': 7,
        'Financial District': 11,
        'Alamo Square': 15,
        'Golden Gate Park': 21,
        'The Castro': 21,
        'Bayview': 23,
        'Sunset District': 23,
        'Haight-Ashbury': 17,
        'Nob Hill': 5
    },
    'Marina District': {
        'Russian Hill': 8,
        'Financial District': 17,
        'Alamo Square': 15,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Sunset District': 19,
        'Haight-Ashbury': 16,
        'Nob Hill': 12
    },
    'Financial District': {
        'Russian Hill': 11,
        'Marina District': 15,
        'Alamo Square': 17,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Nob Hill': 8
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Marina District': 15,
        'Financial District': 17,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Sunset District': 16,
        'Haight-Ashbury': 5,
        'Nob Hill': 11
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Marina District': 16,
        'Financial District': 26,
        'Alamo Square': 9,
        'The Castro': 13,
        'Bayview': 23,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Nob Hill': 20
    },
    'The Castro': {
        'Russian Hill': 18,
        'Marina District': 21,
        'Financial District': 21,
        'Alamo Square': 8,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Sunset District': 17,
        'Haight-Ashbury': 6,
        'Nob Hill': 16
    },
    'Bayview': {
        'Russian Hill': 23,
        'Marina District': 27,
        'Financial District': 19,
        'Alamo Square': 16,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Sunset District': 23,
        'Haight-Ashbury': 19,
        'Nob Hill': 20
    },
    'Sunset District': {
        'Russian Hill': 24,
        'Marina District': 21,
        'Financial District': 30,
        'Alamo Square': 17,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Haight-Ashbury': 15,
        'Nob Hill': 27
    },
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Marina District': 17,
        'Financial District': 21,
        'Alamo Square': 5,
        'Golden Gate Park': 7,
        'The Castro': 6,
        'Bayview': 18,
        'Sunset District': 15,
        'Nob Hill': 15
    },
    'Nob Hill': {
        'Russian Hill': 5,
        'Marina District': 11,
        'Financial District': 9,
        'Alamo Square': 11,
        'Golden Gate Park': 17,
        'The Castro': 17,
        'Bayview': 19,
        'Sunset District': 24,
        'Haight-Ashbury': 13
    }
}

# Friend data
friends = [
    {'name': 'Mark', 'location': 'Marina District', 'start': '18:45', 'end': '21:00', 'duration': 90},
    {'name': 'Karen', 'location': 'Financial District', 'start': '9:30', 'end': '12:45', 'duration': 90},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': '10:00', 'end': '19:30', 'duration': 90},
    {'name': 'Nancy', 'location': 'Golden Gate Park', 'start': '16:45', 'end': '20:00', 'duration': 105},
    {'name': 'David', 'location': 'The Castro', 'start': '9:00', 'end': '18:00', 'duration': 120},
    {'name': 'Linda', 'location': 'Bayview', 'start': '18:15', 'end': '19:45', 'duration': 45},
    {'name': 'Kevin', 'location': 'Sunset District', 'start': '10:00', 'end': '17:45', 'duration': 120},
    {'name': 'Matthew', 'location': 'Haight-Ashbury', 'start': '10:15', 'end': '15:30', 'duration': 45},
    {'name': 'Andrew', 'location': 'Nob Hill', 'start': '11:45', 'end': '16:45', 'duration': 105}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(prev_location, prev_end, friend, current_time):
    travel_time = travel_times[prev_location][friend['location']]
    arrival_time = current_time + travel_time
    friend_start = time_to_minutes(friend['start'])
    friend_end = time_to_minutes(friend['end'])
    
    if arrival_time > friend_end:
        return None
    
    start_time = max(arrival_time, friend_start)
    end_time = start_time + friend['duration']
    
    if end_time > friend_end:
        return None
    
    return (start_time, end_time)

def evaluate_schedule(order):
    current_location = 'Russian Hill'
    current_time = time_to_minutes('9:00')
    itinerary = []
    
    for friend_name in order:
        friend = next(f for f in friends if f['name'] == friend_name)
        schedule = can_schedule(current_location, current_time, friend, current_time)
        if not schedule:
            return None
        start_time, end_time = schedule
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_location = friend['location']
        current_time = end_time
    
    return itinerary

def find_best_schedule():
    friend_names = [f['name'] for f in friends]
    best_schedule = None
    max_meetings = 0
    
    # Try all permutations of 5 friends (to keep computation feasible)
    from itertools import combinations
    for friend_combination in combinations(friend_names, 5):
        for perm in permutations(friend_combination):
            itinerary = evaluate_schedule(perm)
            if itinerary and len(itinerary) > max_meetings:
                max_meetings = len(itinerary)
                best_schedule = itinerary
    
    return best_schedule

best_itinerary = find_best_schedule()
if not best_itinerary:
    best_itinerary = []

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))
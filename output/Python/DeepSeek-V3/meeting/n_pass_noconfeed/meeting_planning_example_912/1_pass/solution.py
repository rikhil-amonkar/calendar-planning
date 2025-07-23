import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Union Square': {
        'Presidio': 24, 'Alamo Square': 15, 'Marina District': 18, 'Financial District': 9,
        'Nob Hill': 9, 'Sunset District': 27, 'Chinatown': 7, 'Russian Hill': 13,
        'North Beach': 10, 'Haight-Ashbury': 18
    },
    'Presidio': {
        'Union Square': 22, 'Alamo Square': 19, 'Marina District': 11, 'Financial District': 23,
        'Nob Hill': 18, 'Sunset District': 15, 'Chinatown': 21, 'Russian Hill': 14,
        'North Beach': 18, 'Haight-Ashbury': 15
    },
    'Alamo Square': {
        'Union Square': 14, 'Presidio': 17, 'Marina District': 15, 'Financial District': 17,
        'Nob Hill': 11, 'Sunset District': 16, 'Chinatown': 15, 'Russian Hill': 13,
        'North Beach': 15, 'Haight-Ashbury': 5
    },
    'Marina District': {
        'Union Square': 16, 'Presidio': 10, 'Alamo Square': 15, 'Financial District': 17,
        'Nob Hill': 12, 'Sunset District': 19, 'Chinatown': 15, 'Russian Hill': 8,
        'North Beach': 11, 'Haight-Ashbury': 16
    },
    'Financial District': {
        'Union Square': 9, 'Presidio': 22, 'Alamo Square': 17, 'Marina District': 15,
        'Nob Hill': 8, 'Sunset District': 30, 'Chinatown': 5, 'Russian Hill': 11,
        'North Beach': 7, 'Haight-Ashbury': 19
    },
    'Nob Hill': {
        'Union Square': 7, 'Presidio': 17, 'Alamo Square': 11, 'Marina District': 11,
        'Financial District': 9, 'Sunset District': 24, 'Chinatown': 6, 'Russian Hill': 5,
        'North Beach': 8, 'Haight-Ashbury': 13
    },
    'Sunset District': {
        'Union Square': 30, 'Presidio': 16, 'Alamo Square': 17, 'Marina District': 21,
        'Financial District': 30, 'Nob Hill': 27, 'Chinatown': 30, 'Russian Hill': 24,
        'North Beach': 28, 'Haight-Ashbury': 15
    },
    'Chinatown': {
        'Union Square': 7, 'Presidio': 19, 'Alamo Square': 17, 'Marina District': 12,
        'Financial District': 5, 'Nob Hill': 9, 'Sunset District': 29, 'Russian Hill': 7,
        'North Beach': 3, 'Haight-Ashbury': 19
    },
    'Russian Hill': {
        'Union Square': 10, 'Presidio': 14, 'Alamo Square': 15, 'Marina District': 7,
        'Financial District': 11, 'Nob Hill': 5, 'Sunset District': 23, 'Chinatown': 9,
        'North Beach': 5, 'Haight-Ashbury': 17
    },
    'North Beach': {
        'Union Square': 7, 'Presidio': 17, 'Alamo Square': 16, 'Marina District': 9,
        'Financial District': 8, 'Nob Hill': 7, 'Sunset District': 27, 'Chinatown': 6,
        'Russian Hill': 4, 'Haight-Ashbury': 18
    },
    'Haight-Ashbury': {
        'Union Square': 19, 'Presidio': 15, 'Alamo Square': 5, 'Marina District': 17,
        'Financial District': 21, 'Nob Hill': 15, 'Sunset District': 15, 'Chinatown': 19,
        'Russian Hill': 17, 'North Beach': 19
    }
}

# Friend availability
friends = [
    {'name': 'Kimberly', 'location': 'Presidio', 'start': '15:30', 'end': '16:00', 'min_duration': 15},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': '19:15', 'end': '20:15', 'min_duration': 15},
    {'name': 'Joshua', 'location': 'Marina District', 'start': '10:30', 'end': '14:15', 'min_duration': 45},
    {'name': 'Sandra', 'location': 'Financial District', 'start': '19:30', 'end': '20:15', 'min_duration': 45},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'start': '12:45', 'end': '21:45', 'min_duration': 30},
    {'name': 'Betty', 'location': 'Sunset District', 'start': '14:00', 'end': '19:00', 'min_duration': 60},
    {'name': 'Deborah', 'location': 'Chinatown', 'start': '17:15', 'end': '20:30', 'min_duration': 15},
    {'name': 'Barbara', 'location': 'Russian Hill', 'start': '17:30', 'end': '21:15', 'min_duration': 120},
    {'name': 'Steven', 'location': 'North Beach', 'start': '17:45', 'end': '20:45', 'min_duration': 90},
    {'name': 'Daniel', 'location': 'Haight-Ashbury', 'start': '18:30', 'end': '18:45', 'min_duration': 15}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(current_time, friend, from_location):
    location = friend['location']
    travel_time = travel_times[from_location][location]
    arrival_time = current_time + travel_time
    friend_start = time_to_minutes(friend['start'])
    friend_end = time_to_minutes(friend['end'])
    min_duration = friend['min_duration']
    
    if arrival_time > friend_end:
        return None
    
    start_time = max(arrival_time, friend_start)
    end_time = min(start_time + min_duration, friend_end)
    
    if end_time - start_time >= min_duration:
        return (start_time, end_time)
    return None

def evaluate_schedule(order):
    current_location = 'Union Square'
    current_time = time_to_minutes('9:00')
    itinerary = []
    met_friends = set()
    
    for friend in order:
        schedule = can_schedule(current_time, friend, current_location)
        if schedule:
            start, end = schedule
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            met_friends.add(friend['name'])
            current_time = end
            current_location = friend['location']
    
    return len(met_friends), itinerary

# Generate all possible orders and evaluate them
best_count = 0
best_itinerary = []

# Since trying all permutations is computationally expensive, we'll try a subset
# Here we prioritize friends with tighter time windows first
priority_order = sorted(friends, key=lambda x: (time_to_minutes(x['end']) - time_to_minutes(x['start'])))

# Try different permutations around the priority order
for attempt in range(1000):
    # Shuffle the order while keeping some priority
    import random
    if attempt < 500:
        # First 500 attempts: shuffle all
        order = random.sample(friends, len(friends))
    else:
        # Next 500 attempts: shuffle but keep first few priority friends
        order = priority_order[:3] + random.sample(priority_order[3:], len(priority_order)-3)
    
    count, itinerary = evaluate_schedule(order)
    if count > best_count or (count == best_count and len(itinerary) > len(best_itinerary)):
        best_count = count
        best_itinerary = itinerary

# Output the best itinerary found
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))
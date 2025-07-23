import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'Presidio': {
        'Marina District': 11,
        'The Castro': 21,
        'Fisherman\'s Wharf': 19,
        'Bayview': 31,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Alamo Square': 19,
        'Golden Gate Park': 12
    },
    'Marina District': {
        'Presidio': 10,
        'The Castro': 22,
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Pacific Heights': 7,
        'Mission District': 20,
        'Alamo Square': 15,
        'Golden Gate Park': 18
    },
    'The Castro': {
        'Presidio': 20,
        'Marina District': 21,
        'Fisherman\'s Wharf': 24,
        'Bayview': 19,
        'Pacific Heights': 16,
        'Mission District': 7,
        'Alamo Square': 8,
        'Golden Gate Park': 11
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Marina District': 9,
        'The Castro': 27,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Mission District': 22,
        'Alamo Square': 21,
        'Golden Gate Park': 25
    },
    'Bayview': {
        'Presidio': 32,
        'Marina District': 27,
        'The Castro': 19,
        'Fisherman\'s Wharf': 25,
        'Pacific Heights': 23,
        'Mission District': 13,
        'Alamo Square': 16,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Marina District': 6,
        'The Castro': 16,
        'Fisherman\'s Wharf': 13,
        'Bayview': 22,
        'Mission District': 15,
        'Alamo Square': 10,
        'Golden Gate Park': 15
    },
    'Mission District': {
        'Presidio': 25,
        'Marina District': 19,
        'The Castro': 7,
        'Fisherman\'s Wharf': 22,
        'Bayview': 14,
        'Pacific Heights': 16,
        'Alamo Square': 11,
        'Golden Gate Park': 17
    },
    'Alamo Square': {
        'Presidio': 17,
        'Marina District': 15,
        'The Castro': 8,
        'Fisherman\'s Wharf': 19,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Golden Gate Park': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Marina District': 16,
        'The Castro': 13,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Mission District': 17,
        'Alamo Square': 9
    }
}

# Friend constraints
friends = [
    {'name': 'Amanda', 'location': 'Marina District', 'start': '14:45', 'end': '19:30', 'duration': 105},
    {'name': 'Melissa', 'location': 'The Castro', 'start': '9:30', 'end': '17:00', 'duration': 30},
    {'name': 'Jeffrey', 'location': 'Fisherman\'s Wharf', 'start': '12:45', 'end': '18:45', 'duration': 120},
    {'name': 'Matthew', 'location': 'Bayview', 'start': '10:15', 'end': '13:15', 'duration': 30},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': '17:00', 'end': '21:30', 'duration': 105},
    {'name': 'Karen', 'location': 'Mission District', 'start': '17:30', 'end': '20:30', 'duration': 105},
    {'name': 'Robert', 'location': 'Alamo Square', 'start': '11:15', 'end': '17:30', 'duration': 120},
    {'name': 'Joseph', 'location': 'Golden Gate Park', 'start': '8:30', 'end': '21:15', 'duration': 105}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(prev_location, prev_end, friend, current_time):
    location = friend['location']
    start = time_to_minutes(friend['start'])
    end = time_to_minutes(friend['end'])
    duration = friend['duration']
    
    travel_time = travel_times[prev_location][location] if prev_location else 0
    arrival_time = current_time + travel_time
    
    if arrival_time > end:
        return None
    
    meet_start = max(arrival_time, start)
    meet_end = meet_start + duration
    
    if meet_end > end:
        return None
    
    return meet_start, meet_end

def evaluate_schedule(order):
    current_location = 'Presidio'
    current_time = time_to_minutes('9:00')
    itinerary = []
    
    for friend in order:
        result = can_schedule(current_location, current_time, friend, current_time)
        if not result:
            return None, 0
        meet_start, meet_end = result
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meet_start),
            'end_time': minutes_to_time(meet_end)
        })
        current_location = friend['location']
        current_time = meet_end
    
    return itinerary, len(itinerary)

def find_best_schedule():
    best_itinerary = []
    best_count = 0
    
    # Try all permutations of 5 friends (to keep computation feasible)
    from itertools import combinations
    for friends_subset in combinations(friends, 5):
        for order in permutations(friends_subset):
            itinerary, count = evaluate_schedule(order)
            if count > best_count:
                best_count = count
                best_itinerary = itinerary
    
    return best_itinerary

best_itinerary = find_best_schedule()

# If no schedule found with 5, try fewer
if not best_itinerary:
    for friends_subset in combinations(friends, 4):
        for order in permutations(friends_subset):
            itinerary, count = evaluate_schedule(order)
            if count > best_count:
                best_count = count
                best_itinerary = itinerary

# Output the best found schedule
output = {
    "itinerary": best_itinerary if best_itinerary else []
}

print(json.dumps(output, indent=2))
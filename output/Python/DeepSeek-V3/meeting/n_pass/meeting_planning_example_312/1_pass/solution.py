import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Richmond District': {
        'Sunset District': 11,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Richmond District': 12,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11
    },
    'Haight-Ashbury': {
        'Richmond District': 10,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Richmond District': 20,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17
    }
}

# Friend constraints
friends = {
    'Sarah': {
        'location': 'Sunset District',
        'available_start': '10:45',
        'available_end': '19:00',
        'duration': 30
    },
    'Richard': {
        'location': 'Haight-Ashbury',
        'available_start': '11:45',
        'available_end': '15:45',
        'duration': 90
    },
    'Elizabeth': {
        'location': 'Mission District',
        'available_start': '11:00',
        'available_end': '17:15',
        'duration': 120
    },
    'Michelle': {
        'location': 'Golden Gate Park',
        'available_start': '18:15',
        'available_end': '20:45',
        'duration': 90
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Richmond District'
    itinerary = []
    
    for friend_name in order:
        friend = friends[friend_name]
        destination = friend['location']
        travel_time = travel_times[current_location][destination]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        duration = friend['duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time > available_end:
            return None
        
        itinerary.append({
            'action': 'meet',
            'location': destination,
            'person': friend_name,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = destination
    
    # Check if Michelle is met last (required)
    if order[-1] != 'Michelle':
        return None
    
    return itinerary

def generate_all_orders():
    # Michelle must be last
    remaining_friends = ['Sarah', 'Richard', 'Elizabeth']
    all_orders = []
    for perm in permutations(remaining_friends):
        all_orders.append(list(perm) + ['Michelle'])
    return all_orders

def find_best_schedule():
    best_schedule = None
    max_meetings = 0
    
    for order in generate_all_orders():
        schedule = calculate_schedule(order)
        if schedule and len(schedule) > max_meetings:
            best_schedule = schedule
            max_meetings = len(schedule)
    
    return best_schedule

best_schedule = find_best_schedule()
if best_schedule is None:
    # Try with fewer meetings if all 4 is impossible
    for num_meetings in [3, 2, 1]:
        for order in generate_all_orders():
            for subset_order in permutations(order, num_meetings):
                # Ensure Michelle is included if present
                if 'Michelle' in subset_order and subset_order[-1] != 'Michelle':
                    continue
                schedule = calculate_schedule(subset_order)
                if schedule:
                    best_schedule = schedule
                    break
            if best_schedule:
                break
        if best_schedule:
            break

if best_schedule is None:
    best_schedule = []

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
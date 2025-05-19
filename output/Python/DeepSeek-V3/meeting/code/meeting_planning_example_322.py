import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'Chinatown': 30,
        'Presidio': 16,
        'Fisherman\'s Wharf': 29
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Fisherman\'s Wharf': 7
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'Presidio': 19,
        'Fisherman\'s Wharf': 8
    },
    'Presidio': {
        'Sunset District': 15,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Fisherman\'s Wharf': 19
    },
    'Fisherman\'s Wharf': {
        'Sunset District': 27,
        'Russian Hill': 7,
        'Chinatown': 12,
        'Presidio': 17
    }
}

# Person constraints
people = {
    'William': {
        'location': 'Russian Hill',
        'available_start': '18:30',
        'available_end': '20:45',
        'min_duration': 105
    },
    'Michelle': {
        'location': 'Chinatown',
        'available_start': '8:15',
        'available_end': '14:00',
        'min_duration': 15
    },
    'George': {
        'location': 'Presidio',
        'available_start': '10:30',
        'available_end': '18:45',
        'min_duration': 30
    },
    'Robert': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:00',
        'available_end': '13:45',
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

def calculate_schedule(order):
    current_location = 'Sunset District'
    current_time = time_to_minutes('9:00')
    schedule = []
    
    for person in order:
        info = people[person]
        location = info['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        min_duration = info['min_duration']
        
        # Calculate meeting window
        start_time = max(arrival_time, available_start)
        end_time = min(start_time + min_duration, available_end)
        
        if end_time - start_time < min_duration:
            return None  # Not enough time to meet
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    total_meetings = len(schedule)
    total_time = sum(time_to_minutes(m['end_time']) - time_to_minutes(m['start_time']) for m in schedule)
    return (total_meetings, total_time)

# Generate all possible orders of meetings
all_orders = permutations(people.keys())
best_schedule = None
best_score = (-1, -1)

for order in all_orders:
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# Prepare output
output = {
    "itinerary": best_schedule
} if best_schedule else {"itinerary": []}

print(json.dumps(output, indent=2))
import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from -> to)
travel_times = {
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Fisherman\'s Wharf': 25
    },
    'Embarcadero': {
        'Bayview': 21,
        'Richmond District': 21,
        'Fisherman\'s Wharf': 6
    },
    'Richmond District': {
        'Bayview': 26,
        'Embarcadero': 19,
        'Fisherman\'s Wharf': 18
    },
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Embarcadero': 8,
        'Richmond District': 18
    }
}

# Meeting constraints
constraints = {
    'Jessica': {
        'location': 'Embarcadero',
        'available_start': '16:45',
        'available_end': '19:00',
        'min_duration': 30
    },
    'Sandra': {
        'location': 'Richmond District',
        'available_start': '18:30',
        'available_end': '21:45',
        'min_duration': 120
    },
    'Jason': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '16:00',
        'available_end': '16:45',
        'min_duration': 30
    }
}

# Initial state
current_location = 'Bayview'
current_time = time_to_minutes('9:00')
meetings = []

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for person in order:
        const = constraints[person]
        loc_to = const['location']
        travel = travel_times[loc][loc_to]
        arrive_time = time + travel
        
        available_start = time_to_minutes(const['available_start'])
        available_end = time_to_minutes(const['available_end'])
        min_duration = const['min_duration']
        
        # Calculate meeting window
        start = max(arrive_time, available_start)
        end = min(start + min_duration, available_end)
        
        if end - start < min_duration:
            return None  # Not enough time to meet
        
        schedule.append({
            'person': person,
            'location': loc_to,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end),
            'depart_time': end
        })
        
        loc = loc_to
        time = end
    
    return schedule

# Try all possible meeting orders
best_schedule = None
best_meetings = 0

for order in permutations(constraints.keys()):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)

# Prepare output
if best_schedule:
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": meeting['start_time'],
            "end_time": meeting['end_time']
        })
    
    output = {
        "itinerary": itinerary
    }
else:
    output = {
        "itinerary": []
    }

print(json.dumps(output, indent=2))
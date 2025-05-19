import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'Embarcadero': {
        'Presidio': 20,
        'Richmond District': 21,
        'Fisherman\'s Wharf': 6
    },
    'Presidio': {
        'Embarcadero': 20,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 19
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Presidio': 7,
        'Fisherman\'s Wharf': 18
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8,
        'Presidio': 17,
        'Richmond District': 18
    }
}

friends = {
    'Betty': {
        'location': 'Presidio',
        'available_start': '10:15',
        'available_end': '21:30',
        'duration': 45
    },
    'David': {
        'location': 'Richmond District',
        'available_start': '13:00',
        'available_end': '20:15',
        'duration': 90
    },
    'Barbara': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:15',
        'available_end': '20:15',
        'duration': 120
    }
}

current_location = 'Embarcadero'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for friend_name in order:
        friend = friends[friend_name]
        dest = friend['location']
        travel_time = travel_times[loc][dest]
        
        # Travel to friend's location
        arrival_time = time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Determine meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > available_end:
            return None  # Doesn't fit
        
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend_name,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        loc = dest
        time = meeting_end
    
    return schedule

# Try all possible orders to find the best schedule
best_schedule = None
best_meetings = 0

for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)
    elif schedule and len(schedule) == best_meetings:
        # Prefer schedules that end earlier
        if not best_schedule or time_to_minutes(schedule[-1]['end_time']) < time_to_minutes(best_schedule[-1]['end_time']):
            best_schedule = schedule

output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))
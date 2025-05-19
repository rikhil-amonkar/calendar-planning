import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
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

friends = {
    'Jessica': {
        'location': 'Embarcadero',
        'start': time_to_minutes('16:45'),
        'end': time_to_minutes('19:00'),
        'duration': 30
    },
    'Sandra': {
        'location': 'Richmond District',
        'start': time_to_minutes('18:30'),
        'end': time_to_minutes('21:45'),
        'duration': 120
    },
    'Jason': {
        'location': 'Fisherman\'s Wharf',
        'start': time_to_minutes('16:00'),
        'end': time_to_minutes('16:45'),
        'duration': 30
    }
}

current_location = 'Bayview'
current_time = time_to_minutes('9:00')

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
max_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for person in order:
        friend = friends[person]
        # Travel to friend's location
        travel_time = travel_times[temp_location][friend['location']]
        arrival_time = temp_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            break  # Can't meet this friend
        
        # Add to schedule
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        meetings += 1
        temp_location = friend['location']
        temp_time = meeting_end
    
    if meetings > max_meetings or (meetings == max_meetings and (best_schedule is None or len(schedule) > len(best_schedule))):
        max_meetings = meetings
        best_schedule = schedule

# Output the best schedule
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
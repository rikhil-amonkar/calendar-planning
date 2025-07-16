import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7
}

friends = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'available_start': '11:45',
        'available_end': '15:15',
        'min_duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'available_start': '16:45',
        'available_end': '18:15',
        'min_duration': 60
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'available_start': '17:15',
        'available_end': '19:00',
        'min_duration': 105
    }
]

current_location = 'The Castro'
current_time = time_to_minutes('9:00')

best_schedule = None
best_meetings = 0

# Generate all possible meeting orders
for meeting_order in permutations(friends):
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for friend in meeting_order:
        # Travel to friend's location
        travel_time = travel_times[(temp_location, friend['location'])]
        arrival_time = temp_time + travel_time
        
        # Check if we can meet the friend
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + friend['min_duration'], available_end)
        
        if meeting_end - meeting_start >= friend['min_duration']:
            # Add meeting to schedule
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1
            temp_location = friend['location']
            temp_time = meeting_end
    
    # Update best schedule if this one is better
    if meetings > best_meetings or (meetings == best_meetings and best_schedule is None):
        best_meetings = meetings
        best_schedule = schedule

# Prepare output
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))
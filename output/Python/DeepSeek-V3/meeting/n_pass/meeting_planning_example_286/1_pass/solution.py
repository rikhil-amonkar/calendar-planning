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
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22
}

friends = {
    'Rebecca': {
        'location': 'Mission District',
        'start': time_to_minutes('11:30'),
        'end': time_to_minutes('20:15'),
        'duration': 120
    },
    'Karen': {
        'location': 'Bayview',
        'start': time_to_minutes('12:45'),
        'end': time_to_minutes('15:00'),
        'duration': 120
    },
    'Carol': {
        'location': 'Sunset District',
        'start': time_to_minutes('10:15'),
        'end': time_to_minutes('11:45'),
        'duration': 30
    }
}

current_location = 'Union Square'
current_time = time_to_minutes('9:00')

# Generate all possible meeting orders
meeting_orders = permutations(['Rebecca', 'Karen', 'Carol'])

best_schedule = None
best_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for person in order:
        friend = friends[person]
        location = friend['location']
        
        # Travel to friend's location
        travel_time = travel_times[(temp_location, location)]
        arrival_time = temp_time + travel_time
        
        # Check if we can meet
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end <= friend['end']:
            # Add meeting to schedule
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': person,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1
            temp_location = location
            temp_time = meeting_end
        else:
            # Can't meet this friend in this order
            break
    
    if meetings > best_meetings:
        best_meetings = meetings
        best_schedule = schedule
    elif meetings == best_meetings and meetings > 0:
        # Prefer schedules that meet more people or have earlier end times
        if not best_schedule or (schedule[-1]['end_time'] < best_schedule[-1]['end_time']):
            best_schedule = schedule

# Output the best schedule
if best_schedule:
    result = {'itinerary': best_schedule}
else:
    result = {'itinerary': []}

print(json.dumps(result, indent=2))
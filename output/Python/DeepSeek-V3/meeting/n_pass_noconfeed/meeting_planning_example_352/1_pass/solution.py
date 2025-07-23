import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from: {to: time})
travel_times = {
    'Union Square': {
        'Nob Hill': 9,
        'Haight-Ashbury': 18,
        'Chinatown': 7,
        'Marina District': 18
    },
    'Nob Hill': {
        'Union Square': 7,
        'Haight-Ashbury': 13,
        'Chinatown': 6,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Union Square': 17,
        'Nob Hill': 15,
        'Chinatown': 19,
        'Marina District': 17
    },
    'Chinatown': {
        'Union Square': 7,
        'Nob Hill': 8,
        'Haight-Ashbury': 19,
        'Marina District': 12
    },
    'Marina District': {
        'Union Square': 16,
        'Nob Hill': 12,
        'Haight-Ashbury': 16,
        'Chinatown': 16
    }
}

# Meeting constraints
meetings = [
    {
        'person': 'Karen',
        'location': 'Nob Hill',
        'available_start': '21:15',
        'available_end': '21:45',
        'duration': 30
    },
    {
        'person': 'Joseph',
        'location': 'Haight-Ashbury',
        'available_start': '12:30',
        'available_end': '19:45',
        'duration': 90
    },
    {
        'person': 'Sandra',
        'location': 'Chinatown',
        'available_start': '7:15',
        'available_end': '19:15',
        'duration': 75
    },
    {
        'person': 'Nancy',
        'location': 'Marina District',
        'available_start': '11:00',
        'available_end': '20:15',
        'duration': 105
    }
]

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    schedule = []
    
    for idx in order:
        meeting = meetings[idx]
        location = meeting['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        duration = meeting['duration']
        
        # Calculate meeting start time
        meeting_start = max(arrival_time, available_start)
        if meeting_start + duration > available_end:
            return None  # Not enough time
        
        meeting_end = meeting_start + duration
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': meeting['person'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    # Count number of meetings (all have equal priority in this problem)
    return len(schedule)

best_schedule = None
best_score = 0

# Try all possible meeting orders (permutations)
for order in permutations(range(len(meetings))):
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# Prepare output
if best_schedule:
    output = {'itinerary': best_schedule}
else:
    output = {'itinerary': []}

print(json.dumps(output, indent=2))
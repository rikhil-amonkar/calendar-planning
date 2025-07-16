import json
from itertools import permutations

# Travel times dictionary: travel_times[from_location][to_location] = minutes
travel_times = {
    'Nob Hill': {
        'Richmond District': 14,
        'Financial District': 9,
        'North Beach': 8,
        'The Castro': 17,
        'Golden Gate Park': 17
    },
    'Richmond District': {
        'Nob Hill': 17,
        'Financial District': 22,
        'North Beach': 17,
        'The Castro': 16,
        'Golden Gate Park': 9
    },
    'Financial District': {
        'Nob Hill': 8,
        'Richmond District': 21,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23
    },
    'North Beach': {
        'Nob Hill': 7,
        'Richmond District': 18,
        'Financial District': 8,
        'The Castro': 22,
        'Golden Gate Park': 22
    },
    'The Castro': {
        'Nob Hill': 16,
        'Richmond District': 16,
        'Financial District': 20,
        'North Beach': 20,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Nob Hill': 20,
        'Richmond District': 7,
        'Financial District': 26,
        'North Beach': 24,
        'The Castro': 13
    }
}

# Friend data: name, location, available start, available end, min duration (minutes)
friends = [
    {'name': 'Emily', 'location': 'Richmond District', 'start': '19:00', 'end': '21:00', 'duration': 15},
    {'name': 'Margaret', 'location': 'Financial District', 'start': '16:30', 'end': '20:15', 'duration': 75},
    {'name': 'Ronald', 'location': 'North Beach', 'start': '18:30', 'end': '19:30', 'duration': 45},
    {'name': 'Deborah', 'location': 'The Castro', 'start': '13:45', 'end': '21:15', 'duration': 90},
    {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'start': '11:15', 'end': '14:30', 'duration': 120}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(sequence, current_time):
    itinerary = []
    current_location = 'Nob Hill'
    current_time_min = time_to_minutes('9:00')
    
    for friend in sequence:
        # Travel to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time_min + travel_time
        
        # Calculate meeting window
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        
        # Determine actual meeting start (max of arrival and friend start)
        meeting_start = max(arrival_time, friend_start)
        
        # Check if we can meet for required duration
        if meeting_start + friend['duration'] > friend_end:
            return None  # Can't meet this friend
        
        meeting_end = meeting_start + friend['duration']
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_location = friend['location']
        current_time_min = meeting_end
    
    return itinerary

def evaluate_schedule(itinerary):
    if not itinerary:
        return 0
    # Count number of friends met
    return len(itinerary)

best_schedule = None
best_score = 0

# Try all possible permutations of friends (since order matters)
for perm in permutations(friends):
    itinerary = can_schedule(perm, '9:00')
    score = evaluate_schedule(itinerary)
    if score > best_score:
        best_score = score
        best_schedule = itinerary

# Output the best schedule found
if best_schedule:
    output = {'itinerary': best_schedule}
else:
    output = {'itinerary': []}

print(json.dumps(output, indent=2))
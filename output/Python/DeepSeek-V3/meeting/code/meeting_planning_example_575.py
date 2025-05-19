import json
from itertools import permutations

def time_to_minutes(time_str):
    """Convert time string 'H:MM' to minutes since midnight."""
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string 'H:MM'."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    'The Castro': {
        'Presidio': 20,
        'Sunset District': 17,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Golden Gate Park': 11,
        'Russian Hill': 18
    },
    'Presidio': {
        'The Castro': 21,
        'Sunset District': 15,
        'Haight-Ashbury': 15,
        'Mission District': 26,
        'Golden Gate Park': 12,
        'Russian Hill': 14
    },
    'Sunset District': {
        'The Castro': 17,
        'Presidio': 16,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11,
        'Russian Hill': 24
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Presidio': 15,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7,
        'Russian Hill': 17
    },
    'Mission District': {
        'The Castro': 7,
        'Presidio': 25,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17,
        'Russian Hill': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Presidio': 11,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Russian Hill': 19
    },
    'Russian Hill': {
        'The Castro': 21,
        'Presidio': 14,
        'Sunset District': 23,
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Golden Gate Park': 21
    }
}

# Friend constraints
friends = [
    {
        'name': 'Rebecca',
        'location': 'Presidio',
        'available_start': '18:15',
        'available_end': '20:45',
        'min_duration': 60
    },
    {
        'name': 'Linda',
        'location': 'Sunset District',
        'available_start': '15:30',
        'available_end': '19:45',
        'min_duration': 30
    },
    {
        'name': 'Elizabeth',
        'location': 'Haight-Ashbury',
        'available_start': '17:15',
        'available_end': '19:30',
        'min_duration': 105
    },
    {
        'name': 'William',
        'location': 'Mission District',
        'available_start': '13:15',
        'available_end': '19:30',
        'min_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Golden Gate Park',
        'available_start': '14:15',
        'available_end': '21:30',
        'min_duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Russian Hill',
        'available_start': '10:00',
        'available_end': '21:15',
        'min_duration': 75
    }
]

def calculate_schedule(start_time, current_location, remaining_friends, visited, current_schedule):
    if not remaining_friends:
        return current_schedule
    
    best_schedule = None
    max_meetings = 0
    
    for friend in remaining_friends:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = start_time + travel_time
        
        # Check if we can meet this friend
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Determine meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + friend['min_duration'], available_end)
        
        if meeting_end - meeting_start >= friend['min_duration']:
            new_visited = visited.copy()
            new_visited.add(friend['name'])
            
            new_schedule = current_schedule.copy()
            new_schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            next_remaining = [f for f in remaining_friends if f['name'] not in new_visited]
            result_schedule = calculate_schedule(
                meeting_end,
                friend['location'],
                next_remaining,
                new_visited,
                new_schedule
            )
            
            if result_schedule and len(result_schedule) > max_meetings:
                max_meetings = len(result_schedule)
                best_schedule = result_schedule
    
    return best_schedule

# Start at The Castro at 9:00 AM (540 minutes)
initial_time = time_to_minutes('9:00')
initial_location = 'The Castro'

# Try all permutations to find the best schedule
best_schedule = None
max_meetings = 0

# We'll try a subset of permutations to make it computationally feasible
from itertools import islice
for perm in islice(permutations(friends), 1000):  # Limit permutations for practicality
    schedule = calculate_schedule(initial_time, initial_location, perm, set(), [])
    if schedule and len(schedule) > max_meetings:
        max_meetings = len(schedule)
        best_schedule = schedule

if not best_schedule:
    # Fallback to meeting as many as possible in order
    best_schedule = calculate_schedule(initial_time, initial_location, friends, set(), [])

# Prepare the output
output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))
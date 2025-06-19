import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02}"

# Define travel times
travel_times = {
    'Union Square': {
        'Golden Gate Park': 22,
        'Pacific Heights': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'The Castro': 19
    },
    'Golden Gate Park': {
        'Union Square': 22,
        'Pacific Heights': 16,
        'Presidio': 11,
        'Chinatown': 23,
        'The Castro': 13
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Presidio': 11,
        'Chinatown': 11,
        'The Castro': 16
    },
    'Presidio': {
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Pacific Heights': 11,
        'Chinatown': 21,
        'The Castro': 21
    },
    'Chinatown': {
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Pacific Heights': 10,
        'Presidio': 19,
        'The Castro': 22
    },
    'The Castro': {
        'Union Square': 19,
        'Golden Gate Park': 11,
        'Pacific Heights': 16,
        'Presidio': 20,
        'Chinatown': 20
    }
}

# Define friends with constraints
friends = [
    {'name': 'Andrew', 'location': 'Golden Gate Park', 'start_available': time_to_minutes('11:45'), 'end_available': time_to_minutes('14:30'), 'min_duration': 75},
    {'name': 'Sarah', 'location': 'Pacific Heights', 'start_available': time_to_minutes('16:15'), 'end_available': time_to_minutes('18:45'), 'min_duration': 15},
    {'name': 'Nancy', 'location': 'Presidio', 'start_available': time_to_minutes('17:30'), 'end_available': time_to_minutes('19:15'), 'min_duration': 60},
    {'name': 'Rebecca', 'location': 'Chinatown', 'start_available': time_to_minutes('9:45'), 'end_available': time_to_minutes('21:30'), 'min_duration': 90},
    {'name': 'Robert', 'location': 'The Castro', 'start_available': time_to_minutes('8:30'), 'end_available': time_to_minutes('14:15'), 'min_duration': 30}
]

initial_location = 'Union Square'
initial_time = time_to_minutes('9:00')  # 9:00 AM

# Generate all permutations of friends
all_perms = list(itertools.permutations(friends))
best_schedule = None
best_count = 0
best_wait = float('inf')

for perm in all_perms:
    current_location = initial_location
    current_time = initial_time
    itinerary = []
    count = 0
    total_wait = 0
    
    for friend in perm:
        # Get travel time from current location to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Skip if we arrive after the friend's availability ends
        if arrival_time > friend['end_available']:
            continue
        
        # Calculate meeting start time (max of arrival and friend's start available)
        start_meeting = max(arrival_time, friend['start_available'])
        # Check if meeting can be scheduled within the friend's availability
        if start_meeting + friend['min_duration'] > friend['end_available']:
            continue
        
        # Calculate wait time at the location (if any)
        wait_time = start_meeting - arrival_time
        total_wait += wait_time
        end_meeting = start_meeting + friend['min_duration']
        
        # Add meeting to itinerary
        meeting = {
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        }
        itinerary.append(meeting)
        
        # Update current location and time
        current_location = friend['location']
        current_time = end_meeting
        count += 1
    
    # Update best schedule if this permutation yields more meetings or same meetings with less waiting
    if count > best_count or (count == best_count and total_wait < best_wait):
        best_count = count
        best_schedule = itinerary
        best_wait = total_wait

# Output the best schedule as JSON
result = {"itinerary": best_schedule}
print(json.dumps(result))
import json
from itertools import permutations

# Convert time string to minutes since midnight
def time_to_minutes(time_str):
    if time_str.endswith('AM') or time_str.endswith('PM'):
        time_str, period = time_str[:-2].strip(), time_str[-2:]
        hours, minutes = map(int, time_str.split(':'))
        if period == 'PM' and hours != 12:
            hours += 12
        if period == 'AM' and hours == 12:
            hours = 0
        return hours * 60 + minutes
    else:
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

# Convert minutes since midnight to time string
def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary
travel_times = {
    'The Castro': {
        'Alamo Square': 8,
        'Richmond District': 16,
        'Financial District': 21,
        'Union Square': 19,
        'Fisherman\'s Wharf': 24,
        'Marina District': 21,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Pacific Heights': 16,
        'Golden Gate Park': 11
    },
    'Alamo Square': {
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 14,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
        'Haight-Ashbury': 5,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Golden Gate Park': 9
    },
    'Richmond District': {
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Fisherman\'s Wharf': 18,
        'Marina District': 9,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Pacific Heights': 10,
        'Golden Gate Park': 9
    },
    'Financial District': {
        'The Castro': 20,
        'Alamo Square': 17,
        'Richmond District': 21,
        'Union Square': 9,
        'Fisherman\'s Wharf': 10,
        'Marina District': 15,
        'Haight-Ashbury': 19,
        'Mission District': 17,
        'Pacific Heights': 13,
        'Golden Gate Park': 23
    },
    'Union Square': {
        'The Castro': 17,
        'Alamo Square': 15,
        'Richmond District': 20,
        'Financial District': 9,
        'Fisherman\'s Wharf': 15,
        'Marina District': 18,
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Golden Gate Park': 22
    },
    'Fisherman\'s Wharf': {
        'The Castro': 27,
        'Alamo Square': 21,
        'Richmond District': 18,
        'Financial District': 11,
        'Union Square': 13,
        'Marina District': 9,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Pacific Heights': 12,
        'Golden Gate Park': 25
    },
    'Marina District': {
        'The Castro': 22,
        'Alamo Square': 15,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 16,
        'Fisherman\'s Wharf': 10,
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Pacific Heights': 7,
        'Golden Gate Park': 18
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Alamo Square': 5,
        'Richmond District': 10,
        'Financial District': 21,
        'Union Square': 19,
        'Fisherman\'s Wharf': 23,
        'Marina District': 17,
        'Mission District': 11,
        'Pacific Heights': 12,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'The Castro': 7,
        'Alamo Square': 11,
        'Richmond District': 20,
        'Financial District': 15,
        'Union Square': 15,
        'Fisherman\'s Wharf': 22,
        'Marina District': 19,
        'Haight-Ashbury': 12,
        'Pacific Heights': 16,
        'Golden Gate Park': 17
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Alamo Square': 10,
        'Richmond District': 12,
        'Financial District': 13,
        'Union Square': 12,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Golden Gate Park': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Alamo Square': 9,
        'Richmond District': 7,
        'Financial District': 26,
        'Union Square': 22,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Pacific Heights': 16
    }
}

# Friend constraints
friends = [
    {'name': 'William', 'location': 'Alamo Square', 'start': '15:15', 'end': '17:15', 'min_duration': 60},
    {'name': 'Joshua', 'location': 'Richmond District', 'start': '7:00', 'end': '20:00', 'min_duration': 15},
    {'name': 'Joseph', 'location': 'Financial District', 'start': '11:15', 'end': '13:30', 'min_duration': 15},
    {'name': 'David', 'location': 'Union Square', 'start': '16:45', 'end': '19:15', 'min_duration': 45},
    {'name': 'Brian', 'location': 'Fisherman\'s Wharf', 'start': '13:45', 'end': '20:45', 'min_duration': 105},
    {'name': 'Karen', 'location': 'Marina District', 'start': '11:30', 'end': '18:30', 'min_duration': 15},
    {'name': 'Anthony', 'location': 'Haight-Ashbury', 'start': '7:15', 'end': '10:30', 'min_duration': 30},
    {'name': 'Matthew', 'location': 'Mission District', 'start': '17:15', 'end': '19:15', 'min_duration': 120},
    {'name': 'Helen', 'location': 'Pacific Heights', 'start': '8:00', 'end': '12:00', 'min_duration': 75},
    {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'start': '19:00', 'end': '21:30', 'min_duration': 60}
]

# Convert all times to minutes
for friend in friends:
    friend['start_min'] = time_to_minutes(friend['start'])
    friend['end_min'] = time_to_minutes(friend['end'])

# Current time starts at 9:00 AM at The Castro
current_time = time_to_minutes('9:00')
current_location = 'The Castro'

itinerary = []

# Helper function to check if a meeting is possible
def can_meet(friend, arrival_time):
    # Calculate available time window
    window_start = max(arrival_time, friend['start_min'])
    window_end = friend['end_min']
    
    # Check if there's enough time for the meeting
    if window_end - window_start >= friend['min_duration']:
        return True, window_start, min(window_end, window_start + friend['min_duration'])
    return False, 0, 0

# Greedy algorithm to schedule meetings
def schedule_meetings():
    global current_time, current_location, itinerary
    
    # Sort friends by end time (earlier first)
    sorted_friends = sorted(friends, key=lambda x: x['end_min'])
    
    for friend in sorted_friends:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        possible, start_time, end_time = can_meet(friend, arrival_time)
        
        if possible:
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            
            # Update current time and location
            current_time = end_time
            current_location = friend['location']

# Try scheduling meetings
schedule_meetings()

# Prepare output
output = {
    "itinerary": itinerary
}

# Print JSON output
print(json.dumps(output, indent=2))
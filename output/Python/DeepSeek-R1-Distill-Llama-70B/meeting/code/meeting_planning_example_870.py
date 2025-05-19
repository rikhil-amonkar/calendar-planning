import itertools
import json

# Define travel times between locations in minutes
travel_times = {
    'Pacific Heights': {
        'Marina District': 6, 'The Castro': 16, 'Richmond District': 12,
        'Alamo Square': 10, 'Financial District': 13, 'Presidio': 11,
        'Mission District': 15, 'Nob Hill': 8, 'Russian Hill': 7
    },
    'Marina District': {
        'Pacific Heights': 7, 'The Castro': 22, 'Richmond District': 11,
        'Alamo Square': 15, 'Financial District': 17, 'Presidio': 10,
        'Mission District': 20, 'Nob Hill': 12, 'Russian Hill': 8
    },
    'The Castro': {
        'Pacific Heights': 16, 'Marina District': 21, 'Richmond District': 16,
        'Alamo Square': 8, 'Financial District': 21, 'Presidio': 20,
        'Mission District': 7, 'Nob Hill': 16, 'Russian Hill': 18
    },
    'Richmond District': {
        'Pacific Heights': 10, 'Marina District': 9, 'The Castro': 16,
        'Alamo Square': 13, 'Financial District': 22, 'Presidio': 7,
        'Mission District': 20, 'Nob Hill': 17, 'Russian Hill': 13
    },
    'Alamo Square': {
        'Pacific Heights': 10, 'Marina District': 15, 'The Castro': 8,
        'Richmond District': 11, 'Financial District': 17, 'Presidio': 17,
        'Mission District': 10, 'Nob Hill': 11, 'Russian Hill': 13
    },
    'Financial District': {
        'Pacific Heights': 13, 'Marina District': 15, 'The Castro': 20,
        'Richmond District': 21, 'Alamo Square': 17, 'Presidio': 22,
        'Mission District': 17, 'Nob Hill': 8, 'Russian Hill': 11
    },
    'Presidio': {
        'Pacific Heights': 11, 'Marina District': 11, 'The Castro': 21,
        'Richmond District': 7, 'Alamo Square': 19, 'Financial District': 23,
        'Mission District': 26, 'Nob Hill': 18, 'Russian Hill': 14
    },
    'Mission District': {
        'Pacific Heights': 16, 'Marina District': 19, 'The Castro': 7,
        'Richmond District': 20, 'Alamo Square': 11, 'Financial District': 15,
        'Presidio': 25, 'Nob Hill': 12, 'Russian Hill': 15
    },
    'Nob Hill': {
        'Pacific Heights': 8, 'Marina District': 11, 'The Castro': 17,
        'Richmond District': 14, 'Alamo Square': 11, 'Financial District': 9,
        'Presidio': 17, 'Mission District': 13, 'Russian Hill': 5
    },
    'Russian Hill': {
        'Pacific Heights': 7, 'Marina District': 7, 'The Castro': 21,
        'Richmond District': 14, 'Alamo Square': 15, 'Financial District': 11,
        'Presidio': 14, 'Mission District': 16, 'Nob Hill': 5
    }
}

# Define friends with their constraints
friends = [
    {'name': 'Linda', 'location': 'Marina District', 'start': 1800, 'end': 2200, 'duration': 30},
    {'name': 'Kenneth', 'location': 'The Castro', 'start': 1645, 'end': 1715, 'duration': 30},
    {'name': 'Kimberly', 'location': 'Richmond District', 'start': 1615, 'end': 2200, 'duration': 30},
    {'name': 'Paul', 'location': 'Alamo Square', 'start': 2160, 'end': 2190, 'duration': 15},
    {'name': 'Carol', 'location': 'Financial District', 'start': 1215, 'end': 1440, 'duration': 60},
    {'name': 'Brian', 'location': 'Presidio', 'start': 1200, 'end': 2130, 'duration': 75},
    {'name': 'Laura', 'location': 'Mission District', 'start': 1915, 'end': 2130, 'duration': 30},
    {'name': 'Sandra', 'location': 'Nob Hill', 'start': 915, 'end': 1830, 'duration': 60},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': 2130, 'end': 2200, 'duration': 75}
]

def convert_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
best_count = 0

# Generate all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Starting at 9:00 AM
    current_loc = 'Pacific Heights'
    itinerary = []
    
    for friend in perm:
        # Calculate travel time to friend's location
        travel = travel_times[current_loc][friend['location']]
        arrival = current_time + travel
        
        # Determine meeting start and end times
        meeting_start = max(arrival, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        # Check if the meeting can be scheduled
        if meeting_end > friend['end']:
            break  # Cannot meet this friend, proceed to next permutation
        
        # Add the meeting to the itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': convert_time(meeting_start),
            'end_time': convert_time(meeting_end)
        })
        
        # Update current time and location for next meeting
        current_time = meeting_end
        current_loc = friend['location']
    
    else:
        # All friends in permutation were successfully scheduled
        if len(itinerary) > best_count:
            best_itinerary = itinerary
            best_count = len(itinerary)

# Prepare the output
output = {
    "itinerary": best_itinerary
}

# Print the result as JSON
print(json.dumps(output, indent=2))
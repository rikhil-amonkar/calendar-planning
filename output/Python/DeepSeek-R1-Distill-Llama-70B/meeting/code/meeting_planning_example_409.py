import itertools
import json

# Define travel times between locations in minutes
travel_times = {
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

# Define friends with their constraints
friends = [
    {'name': 'Thomas', 'location': 'Bayview', 'start': 930, 'end': 1110, 'duration': 120},
    {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': 1110, 'end': 1305, 'duration': 30},
    {'name': 'Laura', 'location': 'Nob Hill', 'start': 525, 'end': 975, 'duration': 30},
    {'name': 'Betty', 'location': 'Marina District', 'start': 1145, 'end': 1305, 'duration': 45},
    {'name': 'Patricia', 'location': 'Embarcadero', 'start': 1050, 'end': 1320, 'duration': 45}
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
    current_loc = 'Fisherman\'s Wharf'
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
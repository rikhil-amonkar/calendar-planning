import itertools
import json

# Define travel times between locations in minutes
travel_times = {
    'Bayview': {
        'North Beach': 22, 'Fisherman\'s Wharf': 25, 'Haight-Ashbury': 19,
        'Nob Hill': 20, 'Golden Gate Park': 22, 'Union Square': 18,
        'Alamo Square': 16, 'Presidio': 32, 'Chinatown': 19, 'Pacific Heights': 23
    },
    'North Beach': {
        'Bayview': 25, 'Fisherman\'s Wharf': 5, 'Haight-Ashbury': 18,
        'Nob Hill': 7, 'Golden Gate Park': 22, 'Union Square': 7,
        'Alamo Square': 16, 'Presidio': 17, 'Chinatown': 6, 'Pacific Heights': 8
    },
    'Fisherman\'s Wharf': {
        'Bayview': 26, 'North Beach': 6, 'Haight-Ashbury': 22,
        'Nob Hill': 11, 'Golden Gate Park': 25, 'Union Square': 13,
        'Alamo Square': 21, 'Presidio': 17, 'Chinatown': 12, 'Pacific Heights': 12
    },
    'Haight-Ashbury': {
        'Bayview': 18, 'North Beach': 19, 'Fisherman\'s Wharf': 23,
        'Nob Hill': 15, 'Golden Gate Park': 7, 'Union Square': 19,
        'Alamo Square': 5, 'Presidio': 15, 'Chinatown': 19, 'Pacific Heights': 12
    },
    'Nob Hill': {
        'Bayview': 19, 'North Beach': 8, 'Fisherman\'s Wharf': 10,
        'Haight-Ashbury': 13, 'Golden Gate Park': 17, 'Union Square': 7,
        'Alamo Square': 11, 'Presidio': 17, 'Chinatown': 6, 'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Bayview': 23, 'North Beach': 23, 'Fisherman\'s Wharf': 24,
        'Haight-Ashbury': 7, 'Nob Hill': 20, 'Union Square': 22,
        'Alamo Square': 9, 'Presidio': 11, 'Chinatown': 23, 'Pacific Heights': 16
    },
    'Union Square': {
        'Bayview': 15, 'North Beach': 10, 'Fisherman\'s Wharf': 15,
        'Haight-Ashbury': 18, 'Nob Hill': 9, 'Golden Gate Park': 22,
        'Alamo Square': 15, 'Presidio': 24, 'Chinatown': 7, 'Pacific Heights': 15
    },
    'Alamo Square': {
        'Bayview': 16, 'North Beach': 15, 'Fisherman\'s Wharf': 19,
        'Haight-Ashbury': 5, 'Nob Hill': 11, 'Golden Gate Park': 9,
        'Union Square': 14, 'Presidio': 17, 'Chinatown': 15, 'Pacific Heights': 10
    },
    'Presidio': {
        'Bayview': 31, 'North Beach': 18, 'Fisherman\'s Wharf': 19,
        'Haight-Ashbury': 15, 'Nob Hill': 18, 'Golden Gate Park': 12,
        'Union Square': 22, 'Alamo Square': 19, 'Chinatown': 21, 'Pacific Heights': 11
    },
    'Chinatown': {
        'Bayview': 20, 'North Beach': 3, 'Fisherman\'s Wharf': 8,
        'Haight-Ashbury': 19, 'Nob Hill': 9, 'Golden Gate Park': 23,
        'Union Square': 7, 'Alamo Square': 17, 'Presidio': 19, 'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Bayview': 22, 'North Beach': 9, 'Fisherman\'s Wharf': 13,
        'Haight-Ashbury': 11, 'Nob Hill': 8, 'Golden Gate Park': 15,
        'Union Square': 12, 'Alamo Square': 10, 'Presidio': 11, 'Chinatown': 11
    }
}

# Define friends with their constraints
friends = [
    {'name': 'Brian', 'location': 'North Beach', 'start': 1300, 'end': 1900, 'duration': 90},
    {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': 1100, 'end': 1245, 'duration': 60},
    {'name': 'Ashley', 'location': 'Haight-Ashbury', 'start': 1500, 'end': 2130, 'duration': 90},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': 1145, 'end': 1830, 'duration': 75},
    {'name': 'Jessica', 'location': 'Golden Gate Park', 'start': 2000, 'end': 2145, 'duration': 105},
    {'name': 'Deborah', 'location': 'Union Square', 'start': 1730, 'end': 2200, 'duration': 60},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'start': 1730, 'end': 2115, 'duration': 45},
    {'name': 'Matthew', 'location': 'Presidio', 'start': 495, 'end': 540, 'duration': 15},
    {'name': 'Kenneth', 'location': 'Chinatown', 'start': 1345, 'end': 2130, 'duration': 105},
    {'name': 'Anthony', 'location': 'Pacific Heights', 'start': 1415, 'end': 1600, 'duration': 30}
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
    current_loc = 'Bayview'
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
import itertools
import json

# Define travel times between locations in minutes
travel_times = {
    'Richmond District': {
        'Chinatown': 20, 'Sunset District': 11, 'Alamo Square': 13,
        'Financial District': 22, 'North Beach': 17, 'Embarcadero': 19,
        'Presidio': 7, 'Golden Gate Park': 9, 'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20, 'Sunset District': 29, 'Alamo Square': 17,
        'Financial District': 5, 'North Beach': 3, 'Embarcadero': 5,
        'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12, 'Chinatown': 30, 'Alamo Square': 17,
        'Financial District': 30, 'North Beach': 28, 'Embarcadero': 30,
        'Presidio': 16, 'Golden Gate Park': 11, 'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11, 'Chinatown': 15, 'Sunset District': 16,
        'Financial District': 17, 'North Beach': 15, 'Embarcadero': 16,
        'Presidio': 17, 'Golden Gate Park': 9, 'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21, 'Chinatown': 5, 'Sunset District': 30,
        'Alamo Square': 17, 'North Beach': 7, 'Embarcadero': 4,
        'Presidio': 22, 'Golden Gate Park': 23, 'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18, 'Chinatown': 6, 'Sunset District': 27,
        'Alamo Square': 16, 'Financial District': 8, 'Embarcadero': 6,
        'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21, 'Chinatown': 7, 'Sunset District': 30,
        'Alamo Square': 19, 'Financial District': 5, 'North Beach': 5,
        'Presidio': 20, 'Golden Gate Park': 25, 'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7, 'Chinatown': 21, 'Sunset District': 15,
        'Alamo Square': 19, 'Financial District': 23, 'North Beach': 18,
        'Embarcadero': 20, 'Golden Gate Park': 12, 'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7, 'Chinatown': 23, 'Sunset District': 10,
        'Alamo Square': 9, 'Financial District': 26, 'North Beach': 23,
        'Embarcadero': 25, 'Presidio': 11, 'Bayview': 23
    },
    'Bayview': {
        'Richmond District': 25, 'Chinatown': 19, 'Sunset District': 23,
        'Alamo Square': 16, 'Financial District': 19, 'North Beach': 22,
        'Embarcadero': 19, 'Presidio': 32, 'Golden Gate Park': 22
    }
}

# Define friends with their constraints
friends = [
    {'name': 'Robert', 'location': 'Chinatown', 'start': 465, 'end': 1710, 'duration': 120},
    {'name': 'David', 'location': 'Sunset District', 'start': 930, 'end': 2265, 'duration': 45},
    {'name': 'Matthew', 'location': 'Alamo Square', 'start': 525, 'end': 1050, 'duration': 90},
    {'name': 'Jessica', 'location': 'Financial District', 'start': 570, 'end': 1980, 'duration': 45},
    {'name': 'Melissa', 'location': 'North Beach', 'start': 435, 'end': 1715, 'duration': 45},
    {'name': 'Mark', 'location': 'Embarcadero', 'start': 1515, 'end': 1740, 'duration': 45},
    {'name': 'Deborah', 'location': 'Presidio', 'start': 2520, 'end': 2685, 'duration': 45},
    {'name': 'Karen', 'location': 'Golden Gate Park', 'start': 2790, 'end': 3600, 'duration': 120},
    {'name': 'Laura', 'location': 'Bayview', 'start': 2915, 'end': 3135, 'duration': 15}
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
    current_loc = 'Richmond District'
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
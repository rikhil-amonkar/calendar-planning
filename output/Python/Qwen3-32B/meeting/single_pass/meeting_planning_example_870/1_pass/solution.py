import itertools
import json

# Define friends with their details
friends = [
    {
        'name': 'Carol',
        'location': 'Financial District',
        'available_start': 615,  # 10:15 AM
        'available_end': 720,    # 12:00 PM
        'min_duration': 60
    },
    {
        'name': 'Brian',
        'location': 'Presidio',
        'available_start': 600,  # 10:00 AM
        'available_end': 1290,   # 9:30 PM
        'min_duration': 75
    },
    {
        'name': 'Sandra',
        'location': 'Nob Hill',
        'available_start': 555,  # 9:15 AM
        'available_end': 1110,   # 6:30 PM
        'min_duration': 60
    },
    {
        'name': 'Kenneth',
        'location': 'The Castro',
        'available_start': 885,  # 2:45 PM
        'available_end': 975,    # 4:15 PM
        'min_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Richmond District',
        'available_start': 855,  # 2:15 PM
        'available_end': 1320,   # 10:00 PM
        'min_duration': 30
    },
    {
        'name': 'Laura',
        'location': 'Mission District',
        'available_start': 975,  # 4:15 PM
        'available_end': 1230,   # 8:30 PM
        'min_duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Marina District',
        'available_start': 1080, # 6:00 PM
        'available_end': 1320,   # 10:00 PM
        'min_duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 1110, # 6:30 PM
        'available_end': 1320,   # 10:00 PM
        'min_duration': 75
    },
    {
        'name': 'Paul',
        'location': 'Alamo Square',
        'available_start': 1260, # 9:00 PM
        'available_end': 1290,   # 9:30 PM
        'min_duration': 15
    }
]

# Define travel times between locations
travel_times = {
    'Pacific Heights': {
        'Marina District': 6,
        'The Castro': 16,
        'Richmond District': 12,
        'Alamo Square': 10,
        'Financial District': 13,
        'Presidio': 11,
        'Mission District': 15,
        'Nob Hill': 8,
        'Russian Hill': 7
    },
    'Marina District': {
        'Pacific Heights': 7,
        'The Castro': 22,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Presidio': 10,
        'Mission District': 20,
        'Nob Hill': 12,
        'Russian Hill': 8
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Presidio': 20,
        'Mission District': 7,
        'Nob Hill': 16,
        'Russian Hill': 18
    },
    'Richmond District': {
        'Pacific Heights': 10,
        'Marina District': 9,
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Presidio': 7,
        'Mission District': 20,
        'Nob Hill': 17,
        'Russian Hill': 13
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Marina District': 15,
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Presidio': 17,
        'Mission District': 10,
        'Nob Hill': 11,
        'Russian Hill': 13
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Marina District': 15,
        'The Castro': 20,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Presidio': 22,
        'Mission District': 17,
        'Nob Hill': 8,
        'Russian Hill': 11
    },
    'Presidio': {
        'Pacific Heights': 11,
        'Marina District': 11,
        'The Castro': 21,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Mission District': 26,
        'Nob Hill': 18,
        'Russian Hill': 14
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Marina District': 19,
        'The Castro': 7,
        'Richmond District': 20,
        'Alamo Square': 11,
        'Financial District': 15,
        'Presidio': 25,
        'Nob Hill': 12,
        'Russian Hill': 15
    },
    'Nob Hill': {
        'Pacific Heights': 8,
        'Marina District': 11,
        'The Castro': 17,
        'Richmond District': 14,
        'Alamo Square': 11,
        'Financial District': 9,
        'Presidio': 17,
        'Mission District': 13,
        'Russian Hill': 5
    },
    'Russian Hill': {
        'Pacific Heights': 7,
        'Marina District': 7,
        'The Castro': 21,
        'Richmond District': 14,
        'Alamo Square': 15,
        'Financial District': 11,
        'Presidio': 14,
        'Mission District': 16,
        'Nob Hill': 5
    }
}

# Initial parameters
start_location = 'Pacific Heights'
start_time_minutes = 540  # 9:00 AM

best_itinerary = []
max_meetings = 0

# Generate all permutations of friends and find the best itinerary
for perm in itertools.permutations(friends):
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    
    for friend in perm:
        # Check if we can travel to this friend's location and meet them
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Determine earliest start time and latest possible start time
        earliest_start = max(arrival_time, friend['available_start'])
        latest_start = friend['available_end'] - friend['min_duration']
        
        if earliest_start > latest_start:
            # Cannot meet this friend, skip
            continue
        
        # Schedule the meeting
        start_time = earliest_start
        end_time = start_time + friend['min_duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': f"{start_time // 60}:{start_time % 60:02d}",
            'end_time': f"{end_time // 60}:{end_time % 60:02d}"
        })
        
        # Update current time and location
        current_time = end_time
        current_location = friend['location']
    
    # Check if this itinerary is better than the current best
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary
    elif len(itinerary) == max_meetings and max_meetings > 0:
        # Choose the itinerary with the earliest end time
        current_end_time = current_time
        best_end_time = int(best_itinerary[-1]['end_time'].replace(':', '')) if best_itinerary else 0
        
        if current_end_time < best_end_time:
            best_itinerary = itinerary

# Output the best itinerary as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
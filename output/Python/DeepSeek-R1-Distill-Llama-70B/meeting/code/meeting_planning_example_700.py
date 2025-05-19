import itertools

# Travel times in minutes between locations
travel_times = {
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'North Beach'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'North Beach'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 15,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'North Beach'): 28,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'North Beach'): 8,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Nob Hill'): 7,
}

# List of friends with their meeting details
# Times converted to minutes since midnight
friends = [
    {'name': 'Kevin', 'location': 'Pacific Heights', 'start': 435, 'end': 525, 'duration': 90},
    {'name': 'Michelle', 'location': 'Golden Gate Park', 'start': 1200, 'end': 1260, 'duration': 15},
    {'name': 'Emily', 'location': 'Fisherman\'s Wharf', 'start': 1035, 'end': 1320, 'duration': 30},
    {'name': 'Mark', 'location': 'Marina District', 'start': 1125, 'end': 1305, 'duration': 75},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': 1020, 'end': 1320, 'duration': 120},
    {'name': 'Laura', 'location': 'Sunset District', 'start': 1260, 'end': 1470, 'duration': 75},
    {'name': 'Mary', 'location': 'Nob Hill', 'start': 1050, 'end': 1200, 'duration': 45},
    {'name': 'Helen', 'location': 'North Beach', 'start': 660, 'end': 780, 'duration': 45},
]

max_meetings = 0
best_itinerary = []

# Generate all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Starting at 9:00 AM
    current_location = 'Presidio'
    itinerary = []
    
    for friend in perm:
        # Calculate travel time to friend's location
        travel = travel_times.get((current_location, friend['location']), None)
        if travel is None:
            break  # No travel time available
        
        arrival_time = current_time + travel
        if arrival_time > friend['end']:
            break  # Cannot meet this friend
        
        # Determine the start and end times for the meeting
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + friend['duration']
        
        if end_time > friend['end']:
            break  # Meeting exceeds friend's availability
        
        # Format times correctly
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(start_time),
            'end_time': format_time(end_time)
        })
        
        current_time = end_time
        current_location = friend['location']
    
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

# Prepare the result
result = {
    "itinerary": best_itinerary
}

# Print the result
print(result)
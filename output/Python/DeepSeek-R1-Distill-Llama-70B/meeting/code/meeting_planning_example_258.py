import itertools

# Travel times in minutes between locations
travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# List of friends with their meeting details
# Times converted to minutes since midnight
friends = [
    {'name': 'Betty', 'location': 'Presidio', 'start': 615, 'end': 1710, 'duration': 45},
    {'name': 'David', 'location': 'Richmond District', 'start': 780, 'end': 1470, 'duration': 90},
    {'name': 'Barbara', 'location': 'Fisherman\'s Wharf', 'start': 555, 'end': 1470, 'duration': 120},
]

max_meetings = 0
best_itinerary = []

# Generate all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Starting at 9:00 AM
    current_location = 'Embarcadero'
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
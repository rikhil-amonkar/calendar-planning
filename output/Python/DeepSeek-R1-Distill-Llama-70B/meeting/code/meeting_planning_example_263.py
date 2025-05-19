import itertools

# Travel times in minutes between locations
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
}

# List of friends with their meeting details
# Times converted to minutes since midnight
friends = [
    {'name': 'Betty', 'location': 'Embarcadero', 'start': 1125, 'end': 1415, 'duration': 15},
    {'name': 'Karen', 'location': 'Fisherman\'s Wharf', 'start': 555, 'end': 945, 'duration': 30},
    {'name': 'Anthony', 'location': 'Financial District', 'start': 555, 'end': 1710, 'duration': 105},
]

max_meetings = 0
best_itinerary = []

# Generate all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Starting at 9:00 AM
    current_location = 'Bayview'
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
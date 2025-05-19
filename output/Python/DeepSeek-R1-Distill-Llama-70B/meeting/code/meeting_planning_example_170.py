import itertools

# Travel times in minutes between locations
travel_times = {
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
}

# List of friends with their meeting details
friends = [
    {'name': 'Emily', 'location': 'Union Square', 'start': 1020, 'end': 1155, 'duration': 45},
    {'name': 'Margaret', 'location': 'Russian Hill', 'start': 1260, 'end': 1440, 'duration': 120},
]

max_meetings = 0
best_itinerary = []

# Generate all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Starting at 9:00 AM (540 minutes since midnight)
    current_location = 'North Beach'
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
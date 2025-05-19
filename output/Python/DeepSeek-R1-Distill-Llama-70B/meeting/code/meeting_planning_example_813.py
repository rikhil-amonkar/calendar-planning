import itertools

# Travel times in minutes between locations
travel_times = {
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Mission District'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
}

# List of friends with their meeting details
friends = [
    {'name': 'Joshua', 'location': 'Embarcadero', 'start': 570, 'end': 1080, 'duration': 105},
    {'name': 'Jeffrey', 'location': 'Bayview', 'start': 570, 'end': 1215, 'duration': 75},
    {'name': 'Charles', 'location': 'Union Square', 'start': 645, 'end': 1215, 'duration': 120},
    {'name': 'Joseph', 'location': 'Chinatown', 'start': 420, 'end': 930, 'duration': 60},
    {'name': 'Matthew', 'location': 'Golden Gate Park', 'start': 660, 'end': 1170, 'duration': 45},
    {'name': 'Carol', 'location': 'Financial District', 'start': 645, 'end': 675, 'duration': 15},
    {'name': 'Paul', 'location': 'Haight-Ashbury', 'start': 1155, 'end': 1230, 'duration': 15},
    {'name': 'Rebecca', 'location': 'Mission District', 'start': 1020, 'end': 1305, 'duration': 45},
]

max_meetings = 0
best_itinerary = []

# Generate all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Starting at 9:00 AM
    current_location = 'Marina District'
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
        start_hour = start_time // 60
        start_minute = start_time % 60
        end_hour = end_time // 60
        end_minute = end_time % 60
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': f"{start_hour}:{start_minute:02d}",
            'end_time': f"{end_hour}:{end_minute:02d}"
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
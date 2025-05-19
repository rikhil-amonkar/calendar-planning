import itertools

# Travel times in minutes between locations
travel_times = {
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Embarcadero'): 14,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Embarcadero'): 19,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Embarcadero'): 30,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Embarcadero'): 19,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Embarcadero'): 6,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
}

# List of friends with their meeting details
# Times converted to minutes since midnight
friends = [
    {'name': 'Charles', 'location': 'Bayview', 'start': 690, 'end': 930, 'duration': 45},
    {'name': 'Robert', 'location': 'Sunset District', 'start': 1140, 'end': 1620, 'duration': 30},
    {'name': 'Karen', 'location': 'Richmond District', 'start': 1350, 'end': 1710, 'duration': 60},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': 1035, 'end': 1500, 'duration': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start': 855, 'end': 1410, 'duration': 120},
    {'name': 'Patricia', 'location': 'Haight-Ashbury', 'start': 870, 'end': 1500, 'duration': 45},
    {'name': 'Mark', 'location': 'North Beach', 'start': 840, 'end': 1170, 'duration': 105},
    {'name': 'Melissa', 'location': 'Russian Hill', 'start': 780, 'end': 1410, 'duration': 30},
    {'name': 'Laura', 'location': 'Embarcadero', 'start': 465, 'end': 810, 'duration': 105},
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
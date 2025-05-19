from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9
}

friends = [
    {
        'name': 'Sarah',
        'location': 'Haight-Ashbury',
        'start_time': time(17, 0),
        'end_time': time(20, 30),
        'duration': 105
    },
    {
        'name': 'Patricia',
        'location': 'Sunset District',
        'start_time': time(17, 0),
        'end_time': time(19, 45),
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Marina District',
        'start_time': time(9, 15),
        'end_time': time(10, 45),
        'duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'start_time': time(14, 15),
        'end_time': time(19, 45),
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Union Square',
        'start_time': time(10, 15),
        'end_time': time(21, 45),
        'duration': 15
    }
]

itinerary = []

current_time = time(9, 0)

# Try to meet each friend in the order of their availability
for friend in friends:
    # Check if current_time allows meeting this friend
    if current_time > friend['end_time']:
        continue
    
    # Calculate latest possible start time for this meeting
    latest_start = friend['end_time'] - timedelta(minutes=friend['duration'])
    if latest_start < current_time:
        continue
    
    # Generate possible start times within the window
    possible_start_times = []
    for hour in range(current_time.hour, latest_start.hour + 1):
        for minute in range(0, 60, 15):
            possible_start = time(hour, minute)
            if possible_start < current_time:
                continue
            possible_start_times.append(possible_start)
    
    # Try each possible start time
    for possible_start in possible_start_times:
        # Calculate travel time to the friend's location
        travel_time = distance[('Golden Gate Park', friend['location'])]
        arrival_time = possible_start + timedelta(minutes=travel_time)
        departure_time = arrival_time + timedelta(minutes=friend['duration'])
        
        # Check if arrival and departure fit within the friend's availability
        if arrival_time < friend['start_time'] or departure_time > friend['end_time']:
            continue
        
        # Add this meeting to the itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': possible_start.strftime("%H:%M"),
            'end_time': departure_time.strftime("%H:%M")
        })
        
        # Update current_time to departure_time
        current_time = departure_time
        # Break to proceed to the next friend
        break

# Convert the itinerary list to a dictionary
itinerary_dict = {
    "itinerary": []
}
for item in itinerary:
    start = item['start_time']
    end = item['end_time']
    location = item['location']
    person = item['person']
    itinerary_dict["itinerary"].append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start,
        "end_time": end
    })

print(json.dumps(itinerary_dict))
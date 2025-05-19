from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Presidio'): 20,
}

friends = [
    {
        'name': 'Andrew',
        'location': 'Golden Gate Park',
        'start_time': time(11, 45),
        'end_time': time(14, 30),
        'duration': 75
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'start_time': time(16, 15),
        'end_time': time(18, 45),
        'duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'start_time': time(17, 30),
        'end_time': time(19, 15),
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Chinatown',
        'start_time': time(9, 45),
        'end_time': time(21, 30),
        'duration': 90
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'start_time': time(8, 30),
        'end_time': time(12, 15),
        'duration': 30
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
        travel_time = distance[('Union Square', friend['location'])]
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
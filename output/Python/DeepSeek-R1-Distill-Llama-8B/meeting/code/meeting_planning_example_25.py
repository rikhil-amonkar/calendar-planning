from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Chinatown', 'Golden Gate Park'): 23
}

itinerary = []

# Starting location is Golden Gate Park at 9:00 AM
current_time = time(9, 0)

# Friend's constraints
friends = [
    {
        'name': 'David',
        'location': 'Chinatown',
        'start_time': time(16, 0),
        'end_time': time(20, 45),
        'duration': 105
    }
]

# Try to meet each friend
for friend in friends:
    # Check if current_time allows meeting this friend
    if current_time > friend['end_time']:
        continue
    
    # Calculate latest possible start time for this meeting
    latest_start = friend['end_time'] - timedelta(minutes=friend['duration'])
    if latest_start < current_time:
        continue
    
    # Possible start times are from current_time to latest_start
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
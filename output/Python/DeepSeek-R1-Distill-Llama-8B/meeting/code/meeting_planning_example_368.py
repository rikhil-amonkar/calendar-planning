from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Financial District'): 19,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Financial District'): 11,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7
}

friends = [
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'start_time': time(8, 30),
        'end_time': time(19, 15),
        'duration': 60
    },
    {
        'name': 'Nancy',
        'location': 'Alamo Square',
        'start_time': time(11, 0),
        'end_time': time(16, 0),
        'duration': 90
    },
    {
        'name': 'Jason',
        'location': 'North Beach',
        'start_time': time(16, 45),
        'end_time': time(20, 45),
        'duration': 15
    },
    {
        'name': 'Jeffrey',
        'location': 'Financial District',
        'start_time': time(10, 30),
        'end_time': time(16, 45),
        'duration': 45
    }
]

itinerary = []

current_time = time(9, 0)

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
        travel_time = distance[('Bayview', friend['location'])]
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
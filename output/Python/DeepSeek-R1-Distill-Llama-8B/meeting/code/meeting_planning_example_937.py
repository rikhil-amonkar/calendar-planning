from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Presidio'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Presidio'): 17,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'The Castro'): 21,
}

itinerary = []

# List of friends with their constraints
friends = [
    {'name': 'David', 'location': 'Sunset District', 'start_time': time(9, 15), 'end_time': time(22, 0), 'duration': 15},
    {'name': 'Kenneth', 'location': 'Union Square', 'start_time': time(21, 15), 'end_time': time(21, 45), 'duration': 15},
    {'name': 'Patricia', 'location': 'Nob Hill', 'start_time': time(15, 0), 'end_time': time(19, 15), 'duration': 120},
    {'name': 'Mary', 'location': 'Marina District', 'start_time': time(14, 45), 'end_time': time(16, 45), 'duration': 45},
    {'name': 'Charles', 'location': 'Richmond District', 'start_time': time(17, 15), 'end_time': time(21, 0), 'duration': 15},
    {'name': 'Joshua', 'location': 'Financial District', 'start_time': time(14, 30), 'end_time': time(17, 15), 'duration': 90},
    {'name': 'Ronald', 'location': 'Embarcadero', 'start_time': time(18, 15), 'end_time': time(20, 45), 'duration': 30},
    {'name': 'George', 'location': 'The Castro', 'start_time': time(14, 15), 'end_time': time(19, 0), 'duration': 105},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'start_time': time(9, 0), 'end_time': time(12, 30), 'duration': 105},
    {'name': 'William', 'location': 'Presidio', 'start_time': time(7, 0), 'end_time': time(12, 45), 'duration': 60},
]

# Starting location is Russian Hill at 9:00 AM
current_time = time(9, 0)

itinerary = []

# Try to meet as many friends as possible
for friend in friends:
    # Check if this friend's time window is compatible with current_time
    if current_time > friend['end_time']:
        continue
    # Calculate the latest possible start time for this meeting
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
        # Calculate arrival and departure times
        travel_time = distance[('Russian Hill', friend['location'])]
        arrival_time = possible_start + timedelta(minutes=travel_time)
        departure_time = arrival_time + timedelta(minutes=friend['duration'])
        # Check if arrival and departure fit within the friend's availability
        if arrival_time < friend['start_time'] or departure_time > friend['end_time']:
            continue
        # Add the meeting to the itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': possible_start.strftime("%H:%M"),
            'end_time': departure_time.strftime("%H:%M")
        })
        # Update current_time to departure_time
        current_time = departure_time
        # Move to the next friend
        break

# Convert itinerary to dictionary
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
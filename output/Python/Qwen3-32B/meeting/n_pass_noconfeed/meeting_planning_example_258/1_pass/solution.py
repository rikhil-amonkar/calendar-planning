import itertools
import json

def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times between locations
travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Richmond District'): 18,
}

# Define friends with their constraints
friends = [
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': time_to_minutes(9, 15),
        'available_end': time_to_minutes(20, 15),
        'required_duration': 120
    },
    {
        'name': 'Betty',
        'location': 'Presidio',
        'available_start': time_to_minutes(10, 15),
        'available_end': time_to_minutes(21, 30),
        'required_duration': 45
    },
    {
        'name': 'David',
        'location': 'Richmond District',
        'available_start': time_to_minutes(13, 0),
        'available_end': time_to_minutes(20, 15),
        'required_duration': 90
    }
]

# Start at Embarcadero at 9:00 AM (540 minutes)
start_location = 'Embarcadero'
start_time = time_to_minutes(9, 0)

# Generate all permutations of friends and check for valid schedule
for perm in itertools.permutations(friends):
    itinerary = []
    current_location = start_location
    current_time = start_time
    valid = True
    
    for friend in perm:
        # Calculate travel time to friend's location
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            valid = False
            break
        
        current_time += travel_time
        
        # Determine the earliest start time for the meeting
        meeting_start = max(current_time, friend['available_start'])
        
        # Check if there's enough time for the required meeting duration
        if meeting_start + friend['required_duration'] > friend['available_end']:
            valid = False
            break
        
        # Schedule the meeting
        meeting_end = meeting_start + friend['required_duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_end)
        })
        
        # Update current location and time
        current_location = friend['location']
        current_time = meeting_end
    
    if valid:
        # Output the valid itinerary
        print(json.dumps({"itinerary": itinerary}))
        exit()

# If no valid itinerary is found (unlikely here), output empty
print(json.dumps({"itinerary": []}))
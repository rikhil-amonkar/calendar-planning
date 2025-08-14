import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

# Define travel times
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20,
}

# Define friends
friends = [
    {
        'name': 'Timothy',
        'location': 'Embarcadero',
        'available_start': time_to_minutes('9:45'),
        'available_end': time_to_minutes('17:45'),
        'required_duration': 120
    },
    {
        'name': 'Patricia',
        'location': 'Nob Hill',
        'available_start': time_to_minutes('18:30'),
        'available_end': time_to_minutes('21:45'),
        'required_duration': 90
    },
    {
        'name': 'Ashley',
        'location': 'Mission District',
        'available_start': time_to_minutes('20:30'),
        'available_end': time_to_minutes('21:15'),
        'required_duration': 45
    }
]

best_itinerary = []
best_count = 0

# Check all permutations of 1, 2, 3 friends
for r in range(1, 4):
    for perm in itertools.permutations(friends, r):
        current_time = time_to_minutes('9:00')  # Start at 9:00 AM
        current_location = 'Russian Hill'
        valid = True
        itinerary = []
        
        for friend in perm:
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend['location']))
            if travel_time is None:
                valid = False
                break
            arrival_time = current_time + travel_time
            
            # Check if meeting is possible
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required_duration']
            
            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - required
            
            if earliest_start > latest_start:
                valid = False
                break
            
            # Schedule meeting
            meeting_start = earliest_start
            meeting_end = meeting_start + required
            
            # Add to itinerary
            itinerary.append((friend, meeting_start, meeting_end))
            
            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']
        
        if valid:
            if len(itinerary) > best_count:
                best_count = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == best_count and best_itinerary:
                # Compare end times; choose the one that ends earlier
                current_best_end = best_itinerary[-1][2]
                new_end = itinerary[-1][2]
                if new_end < current_best_end:
                    best_itinerary = itinerary

# Convert best itinerary to JSON format
json_itinerary = []
for entry in best_itinerary:
    friend = entry[0]
    start_time = minutes_to_time(entry[1])
    end_time = minutes_to_time(entry[2])
    json_itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

result = {
    "itinerary": json_itinerary
}

print(json.dumps(result, indent=2))
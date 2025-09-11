import itertools
import json

# Define travel times between locations (in minutes)
travel_times = {
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16,
}

# Define friends and their constraints
friends = [
    {
        'name': 'Kenneth',
        'location': 'Mission District',
        'available_start': 720,  # 12:00 PM in minutes
        'available_end': 945,    # 3:45 PM in minutes
        'min_duration': 45
    },
    {
        'name': 'Thomas',
        'location': 'Pacific Heights',
        'available_start': 930,  # 3:30 PM in minutes
        'available_end': 1155,   # 7:15 PM in minutes
        'min_duration': 75
    }
]

# Initial parameters
initial_location = 'Nob Hill'
initial_time = 540  # 9:00 AM in minutes

def mins_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

best_itinerary = None

# Check all permutations of friends
for perm in itertools.permutations(friends):
    current_time = initial_time
    current_location = initial_location
    itinerary = []
    valid = True
    
    for friend in perm:
        # Calculate travel time
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            valid = False
            break
        current_time += travel_time
        
        # Determine meeting start time
        start_time = max(current_time, friend['available_start'])
        
        # Check if meeting is possible
        if start_time + friend['min_duration'] > friend['available_end']:
            valid = False
            break
        
        # Record the meeting
        end_time = start_time + friend['min_duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': mins_to_time(start_time),
            'end_time': mins_to_time(end_time)
        })
        
        # Update current time and location
        current_time = end_time
        current_location = friend['location']
    
    if valid:
        best_itinerary = itinerary
        break  # Take the first valid permutation

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
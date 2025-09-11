import json
from itertools import permutations

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times between locations (minutes)
travel_times = {
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Presidio'): 10,
}

# Friend constraints
friends = [
    {
        'name': 'Jason',
        'location': 'Presidio',
        'available_start': 600,   # 10:00 AM
        'available_end': 975,     # 4:15 PM
        'required_duration': 90
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': 930,   # 3:30 PM
        'available_end': 1005,    # 4:45 PM
        'required_duration': 45
    }
]

start_time = 540  # 9:00 AM in minutes
start_location = 'Pacific Heights'

best_itinerary = None

# Try all possible meeting sequences
for sequence in permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    valid = True
    
    for friend in sequence:
        # Add travel time
        travel_time = travel_times.get((current_location, friend['location']), 0)
        current_time += travel_time
        
        # Calculate meeting time
        meeting_start = max(current_time, friend['available_start'])
        meeting_end = meeting_start + friend['required_duration']
        
        # Check if meeting fits in available window
        if meeting_end > friend['available_end']:
            valid = False
            break
            
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update for next iteration
        current_time = meeting_end
        current_location = friend['location']
    
    if valid:
        best_itinerary = itinerary
        break

# Format output
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))
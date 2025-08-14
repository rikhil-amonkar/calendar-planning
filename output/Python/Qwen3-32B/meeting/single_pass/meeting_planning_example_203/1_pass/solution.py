import itertools
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'available_start': 540,  # 9:00 AM
        'available_end': 930,    # 3:30 PM
        'required_duration': 75
    },
    {
        'name': 'David',
        'location': "Fisherman's Wharf",
        'available_start': 645,  # 10:45 AM
        'available_end': 930,    # 3:30 PM
        'required_duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Mission District',
        'available_start': 735,  # 12:15 PM
        'available_end': 1185,   # 7:45 PM
        'required_duration': 90
    }
]

# Define travel times between locations
travel_times = {
    ('Financial District', "Fisherman's Wharf"): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

best_itinerary = []
max_meetings = 0

# Generate all permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # Start at 9:00 AM
    current_location = 'Financial District'
    itinerary = []
    valid = True
    
    for friend in perm:
        # Calculate travel time
        from_loc = current_location
        to_loc = friend['location']
        travel_time = travel_times.get((from_loc, to_loc))
        if travel_time is None:
            valid = False
            break
        
        current_time += travel_time
        
        # Determine earliest start time for the meeting
        earliest_start = max(current_time, friend['available_start'])
        
        # Check if there's enough time for the meeting
        if earliest_start + friend['required_duration'] > friend['available_end']:
            valid = False
            break
        
        # Schedule the meeting
        end_time = earliest_start + friend['required_duration']
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': earliest_start,
            'end_time': end_time
        })
        
        # Update current time and location
        current_time = end_time
        current_location = to_loc
    
    if valid and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary
    elif valid and len(itinerary) == max_meetings and max_meetings > 0:
        # In case of tie, choose the first one found
        pass

# Convert the best itinerary to the required format
output_itinerary = []
for meeting in best_itinerary:
    output_itinerary.append({
        'action': 'meet',
        'location': meeting['location'],
        'person': meeting['person'],
        'start_time': minutes_to_time(meeting['start_time']),
        'end_time': minutes_to_time(meeting['end_time'])
    })

# Generate the final JSON output
result = {"itinerary": output_itinerary}
print(json.dumps(result, indent=2))